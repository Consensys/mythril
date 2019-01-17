"""The Mythril function signature database."""
import functools
import logging
import multiprocessing
import os
import sqlite3
import time
from collections import defaultdict
from subprocess import PIPE, Popen
from typing import List, Dict, Set

from mythril.exceptions import CompilerError

log = logging.getLogger(__name__)

lock = multiprocessing.Lock()


def synchronized(sync_lock):
    """A decorator synchronizing multi-process access to a resource."""

    def wrapper(f):
        """The decorator's core function.

        :param f:
        :return:
        """

        @functools.wraps(f)
        def inner_wrapper(*args, **kw):
            """

            :param args:
            :param kw:
            :return:
            """
            with sync_lock:
                return f(*args, **kw)

        return inner_wrapper

    return wrapper


class Singleton(type):
    """A metaclass type implementing the singleton pattern."""

    _instances = dict()

    @synchronized(lock)
    def __call__(cls, *args, **kwargs):
        """Delegate the call to an existing resource or a a new one.

        This is not thread- or process-safe by default. It must be protected with
        a lock.

        :param args:
        :param kwargs:
        :return:
        """
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)

        return cls._instances[cls]


try:
    # load if available but do not fail
    import ethereum_input_decoder
    from ethereum_input_decoder.decoder import FourByteDirectoryOnlineLookupError
except ImportError:
    # fake it :)
    ethereum_input_decoder = None
    FourByteDirectoryOnlineLookupError = Exception


class SQLiteDB(object):
    """Simple context manager for sqlite3 databases.

    Commits everything at exit.
    """

    def __init__(self, path):
        """

        :param path:
        """
        self.path = path
        self.conn = None
        self.cursor = None

    def __enter__(self):
        """

        :return:
        """
        self.conn = sqlite3.connect(self.path)
        self.cursor = self.conn.cursor()
        return self.cursor

    def __exit__(self, exc_class, exc, traceback):
        """

        :param exc_class:
        :param exc:
        :param traceback:
        """
        self.conn.commit()
        self.conn.close()

    def __repr__(self):
        return "<SQLiteDB path={}>".format(self.path)


class SignatureDB(object, metaclass=Singleton):
    """"""

    def __init__(self, enable_online_lookup: bool = False, path: str = None) -> None:
        """
        :param enable_online_lookup:
        :param path:
        """
        self.enable_online_lookup = enable_online_lookup
        self.online_lookup_miss = set()
        self.online_lookup_timeout = 0

        # if we're analysing a Solidity file, store its hashes
        # here to prevent unnecessary lookups
        self.solidity_sigs = defaultdict(list)
        if path is None:
            self.path = os.environ.get("MYTHRIL_DIR") or os.path.join(
                os.path.expanduser("~"), ".mythril"
            )
        self.path = os.path.join(self.path, "signatures.db")

        log.info("Using signature database at %s", self.path)
        # NOTE: Creates a new DB file if it doesn't exist already
        with SQLiteDB(self.path) as cur:
            cur.execute(
                (
                    "CREATE TABLE IF NOT EXISTS signatures"
                    "(byte_sig VARCHAR(10), text_sig VARCHAR(255),"
                    "PRIMARY KEY (byte_sig, text_sig))"
                )
            )

    def __getitem__(self, item: str) -> List[str]:
        """Provide dict interface db[sighash]

        :param item: 4-byte signature string
        :return: list of matching text signature strings
        """
        return self.get(byte_sig=item)

    @staticmethod
    def _normalize_byte_sig(byte_sig: str) -> str:
        """Adds a leading 0x to the byte signature if it's not already there.

        :param byte_sig: 4-byte signature string
        :return: normalized byte signature string
        """
        if not byte_sig.startswith("0x"):
            byte_sig = "0x" + byte_sig
        if not len(byte_sig) == 10:
            raise ValueError(
                "Invalid byte signature %s, must have 10 characters", byte_sig
            )
        return byte_sig

    def add(self, byte_sig: str, text_sig: str) -> None:
        """
        Adds a new byte - text signature pair to the database.
        :param byte_sig: 4-byte signature string
        :param text_sig: resolved text signature
        :return:
        """
        byte_sig = self._normalize_byte_sig(byte_sig)
        with SQLiteDB(self.path) as cur:
            # ignore new row if it's already in the DB (and would cause a unique constraint error)
            cur.execute(
                "INSERT OR IGNORE INTO signatures (byte_sig, text_sig) VALUES (?,?)",
                (byte_sig, text_sig),
            )

    def get(self, byte_sig: str, online_timeout: int = 2) -> List[str]:
        """Get a function text signature for a byte signature 1) try local
        cache 2) try online lookup (if enabled; if not flagged as unavailable)

        :param byte_sig: function signature hash as hexstr
        :param online_timeout: online lookup timeout
        :return: list of matching function text signatures
        """

        byte_sig = self._normalize_byte_sig(byte_sig)

        # check if we have any Solidity signatures to look up
        text_sigs = self.solidity_sigs.get(byte_sig)
        if text_sigs is not None:
            return text_sigs

        # try lookup in the local DB
        with SQLiteDB(self.path) as cur:
            cur.execute("SELECT text_sig FROM signatures WHERE byte_sig=?", (byte_sig,))
            text_sigs = cur.fetchall()

        if text_sigs:
            return [t[0] for t in text_sigs]

        # abort if we're not allowed to check 4byte or we already missed
        # the signature, or we're on a timeout
        if (
            not self.enable_online_lookup
            or byte_sig in self.online_lookup_miss
            or time.time() < self.online_lookup_timeout
        ):
            return []

        try:
            text_sigs = self.lookup_online(byte_sig=byte_sig, timeout=online_timeout)
            if not text_sigs:
                self.online_lookup_miss.add(byte_sig)
                return []
            else:
                for resolved in text_sigs:
                    self.add(byte_sig, resolved)
                return text_sigs
        except FourByteDirectoryOnlineLookupError as fbdole:
            # wait at least 2 mins to try again
            self.online_lookup_timeout = time.time() + 2 * 60
            log.warning("Online lookup failed, not retrying for 2min: %s", fbdole)
            return []

    def import_solidity_file(
        self, file_path: str, solc_binary: str = "solc", solc_args: str = None
    ):
        """Import Function Signatures from solidity source files.

        :param solc_binary:
        :param solc_args:
        :param file_path: solidity source code file path
        :return:
        """
        cmd = [solc_binary, "--hashes", file_path]
        if solc_args:
            cmd.extend(solc_args.split())

        try:
            p = Popen(cmd, stdout=PIPE, stderr=PIPE)
            stdout, stderr = p.communicate()
            ret = p.returncode

            if ret != 0:
                raise CompilerError(
                    "Solc has experienced a fatal error (code {}).\n\n{}".format(
                        ret, stderr.decode("utf-8")
                    )
                )
        except FileNotFoundError:
            raise CompilerError(
                (
                    "Compiler not found. Make sure that solc is installed and in PATH, "
                    "or the SOLC environment variable is set."
                )
            )

        stdout = stdout.decode("unicode_escape").split("\n")
        for line in stdout:
            # the ':' need not be checked but just to be sure
            if all(map(lambda x: x in line, ["(", ")", ":"])):
                solc_bytes = "0x" + line.split(":")[0]
                solc_text = line.split(":")[1].strip()
                self.solidity_sigs[solc_bytes].append(solc_text)
        log.debug(
            "Signatures: found %d signatures after parsing" % len(self.solidity_sigs)
        )

        # update DB with what we've found
        for byte_sig, text_sigs in self.solidity_sigs.items():
            for text_sig in text_sigs:
                self.add(byte_sig, text_sig)

    @staticmethod
    def lookup_online(byte_sig: str, timeout: int, proxies=None) -> List[str]:
        """Lookup function signatures from 4byte.directory.

        :param byte_sig: function signature hash as hexstr
        :param timeout: optional timeout for online lookup
        :param proxies: optional proxy servers for online lookup
        :return: a list of matching function signatures for this hash
        """
        if not ethereum_input_decoder:
            return []
        return list(
            ethereum_input_decoder.decoder.FourByteDirectory.lookup_signatures(
                byte_sig, timeout=timeout, proxies=proxies
            )
        )

    def __repr__(self):
        return "<SignatureDB path='{}' enable_online_lookup={}>".format(
            self.path, self.enable_online_lookup
        )
