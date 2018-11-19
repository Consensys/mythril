#!/usr/bin/env python3
# -*- coding: UTF-8 -*-
"""mythril.py: Function Signature Database
"""
import os
import json
import time
import logging
import sqlite3
from typing import List, Dict

from collections import defaultdict
from subprocess import Popen, PIPE
from mythril.exceptions import CompilerError


try:
    # load if available but do not fail
    import ethereum_input_decoder
    from ethereum_input_decoder.decoder import FourByteDirectoryOnlineLookupError
except ImportError:
    # fake it :)
    ethereum_input_decoder = None
    FourByteDirectoryOnlineLookupError = Exception


# try:
#     # Posix based file locking (Linux, Ubuntu, MacOS, etc.)
#     import fcntl
#
#     def lock_file(f, exclusive=False):
#         if f.mode == "r" and exclusive:
#             raise Exception("Please use non exclusive mode for reading")
#         flag = fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH
#         fcntl.lockf(f, flag)
#
#     def unlock_file(f):
#         return
#
#
# except ImportError:
#     # Windows file locking
#     # TODO: confirm the existence or non existence of shared locks in windows msvcrt and make changes based on that
#     import msvcrt
#
#     def file_size(f):
#         return os.path.getsize(os.path.realpath(f.name))
#
#     def lock_file(f, exclusive=False):
#         if f.mode == "r" and exclusive:
#             raise Exception("Please use non exclusive mode for reading")
#         msvcrt.locking(f.fileno(), msvcrt.LK_RLCK, file_size(f))
#
#     def unlock_file(f):
#         msvcrt.locking(f.fileno(), msvcrt.LK_UNLCK, file_size(f))


class SignatureDB(object):
    def __init__(self, enable_online_lookup: bool = False, path: str = None) -> None:
        self.enable_online_lookup = enable_online_lookup
        self.online_lookup_miss = set()
        self.online_lookup_timeout = 0
        if path is None:
            self.path = os.environ.get("MYTHRIL_DIR") or os.path.join(
                os.path.expanduser("~"), ".mythril"
            )
        self.path = os.path.join(self.path, "signatures.db")

        self.conn = sqlite3.connect(self.path)
        cur = self.conn.cursor()
        cur.execute(
            (
                "CREATE TABLE IF NOT EXISTS signatures"
                "(byte_sig VARCHAR(10), text_sig VARCHAR(255),"
                "PRIMARY KEY (byte_sig, text_sig))"
            )
        )
        self.conn.commit()
        cur.close()

    def __del__(self) -> None:
        self.conn.close()

    def __getitem__(self, item: str) -> List[str]:
        """
        Provide dict interface db[sighash]
        :param item: 8-byte signature string
        :return: list of matching text signature strings
        """
        return self.get(byte_sig=item)

    @staticmethod
    def _normalize_byte_sig(byte_sig: str):
        """
        Adds a leading 0x to the byte signature if it's not already there.
        :param byte_sig: 8-byte signature string
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
        :param byte_sig: 8-byte signature string
        :param text_sig: resolved text signature
        :return:
        """
        byte_sig = self._normalize_byte_sig(byte_sig)
        cur = self.conn.cursor()
        # ignore new row if it's already in the DB (and would cause a unique constraint error)
        cur.execute(
            "INSERT OR IGNORE INTO signatures (byte_sig, text_sig) VALUES (?,?)",
            (byte_sig, text_sig),
        )
        self.conn.commit()
        cur.close()

    def get(self, byte_sig: str, online_timeout: int = 2) -> List[str]:
        """
        Get a function text signature for a byte signature
        1) try local cache
        2) try online lookup (if enabled; if not flagged as unavailable)
        :param byte_sig: function signature hash as hexstr
        :param online_timeout: online lookup timeout
        :return: list of matching function text signatures
        """

        byte_sig = self._normalize_byte_sig(byte_sig)
        # try lookup in the local DB
        cur = self.conn.cursor()
        cur.execute("SELECT text_sig FROM signatures WHERE byte_sig=?", (byte_sig,))
        text_sigs = cur.fetchall()
        if text_sigs:
            return [t[0] for t in text_sigs]

        # otherwise try the online lookup if we're allowed to
        if not (
            self.enable_online_lookup
            and byte_sig not in self.online_lookup_miss
            and time.time() > self.online_lookup_timeout,
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
            logging.warning("Online lookup failed, not retrying for 2min: %s", fbdole)
            return []

    def import_solidity_file(self, file_path, solc_binary="solc", solc_args=None):
        """
        Import Function Signatures from solidity source files
        :param file_path: solidity source code file path
        :return:
        """
        sigs = {}
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
            raise CompilerError((
                "Compiler not found. Make sure that solc is installed and in PATH, "
                "or the SOLC environment variable is set."
            ))

        stdout = stdout.decode("unicode_escape").split("\n")
        for line in stdout:
            # the ':' need not be checked but just to be sure
            if all(map(lambda x: x in line, ["(", ")", ":"])):
                sigs["0x" + line.split(":")[0]] = [line.split(":")[1].strip()]

        logging.debug("Signatures: found %d signatures after parsing" % len(sigs))

        if not sigs:
            return

        # update DB
        for byte_sig, text_sigs in sigs.items():
            for text_sig in text_sigs:
                self.add(byte_sig, text_sig)

    @staticmethod
    def lookup_online(byte_sig: str, timeout: int, proxies=None) -> List[str]:
        """
        Lookup function signatures from 4byte.directory.
        //tintinweb: the smart-contract-sanctuary project dumps contracts from etherscan.io and feeds them into
                     4bytes.directory.
                     https://github.com/tintinweb/smart-contract-sanctuary

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


# class Singleton(type):
#     _instances = {}
#
#     def __call__(cls, *args, **kwargs):
#         if cls not in cls._instances:
#             cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
#         return cls._instances[cls]
#
#
# class SignatureDb(object, metaclass=Singleton):
#     def __init__(self, enable_online_lookup=False):
#         """
#         Constr
#         :param enable_online_lookup: enable onlien signature hash lookup
#         """
#         self.signatures = defaultdict(list)  # signatures in-mem cache
#         self.signatures_file = None
#         self.enable_online_lookup = (
#             enable_online_lookup
#         )  # enable online funcsig resolving
#         # temporarily track misses from onlinedb to avoid requesting the same non-existent sighash multiple times
#         self.online_lookup_miss = set()
#         # flag the online directory as unavailable for some time
#         self.online_directory_unavailable_until = 0
#         self.open()
#
#     def open(self, path=None):
#         """
#         Open a function signature db from json file
#
#         :param path: specific path to signatures.json; default mythril location if not specified
#         :return: self
#         """
#         if not path:
#             #  try default locations
#             try:
#                 mythril_dir = os.environ["MYTHRIL_DIR"]
#             except KeyError:
#                 mythril_dir = os.path.join(os.path.expanduser("~"), ".mythril")
#             path = os.path.join(mythril_dir, "signatures.json")
#
#         # store early to allow error handling to access the place we tried to load the file
#         self.signatures_file = path
#         if not os.path.exists(path):
#             logging.debug("Signatures: file not found: %s" % path)
#             raise FileNotFoundError(
#                 (
#                     "Could not find signature file in {}. Function name resolution disabled.\n"
#                     "Consider replacing it with the pre-initialized database at "
#                     "https://raw.githubusercontent.com/ConsenSys/mythril/master/signatures.json"
#                 ).format(path)
#             )
#
#         with open(path, "r") as f:
#             lock_file(f)
#             try:
#                 sigs = json.load(f)
#             except json.JSONDecodeError as e:
#                 # reraise with path
#                 raise json.JSONDecodeError(
#                     "Invalid JSON in the signatures file {}: {}".format(path, str(e))
#                 )
#             finally:
#                 unlock_file(f)
#
#         # assert signature file format
#         for sighash, funcsig in sigs.items():
#             if (
#                 not sighash.startswith("0x")
#                 or len(sighash) != 10
#                 or not isinstance(funcsig, list)
#             ):
#                 raise ValueError(
#                     "Malformed signature file at {}. {}: {} is not a valid entry".format(
#                         path, sighash, funcsig
#                     )
#                 )
#         self.signatures = defaultdict(list, sigs)
#
#         return self
#
#     def update_signatures(self, new_signatures):
#         for sighash, funcsigs in new_signatures.items():
#             # eliminate duplicates
#             updated_funcsigs = set(funcsigs + self.signatures[sighash])
#             self.signatures[sighash] = list(updated_funcsigs)
#
#     def write(self, path=None, sync=True):
#         """
#         Write signatures database as json to file
#
#         :param path: specify path otherwise update the file that was loaded with open()
#         :param sync: lock signature file, load contents and merge it into memcached sighash db, then save it
#         :return: self
#         """
#         path = path or self.signatures_file
#         directory = os.path.split(path)[0]
#
#         if sync and os.path.exists(path):
#             # reload and save if file exists
#             with open(path, "r") as f:
#                 lock_file(f)
#                 try:
#                     sigs = json.load(f)
#                 finally:
#                     unlock_file(f)
#
#             self.update_signatures(sigs)
#
#         if directory and not os.path.exists(directory):
#             os.makedirs(directory)  # create folder structure if not existS
#
#         if not os.path.exists(path):  # creates signatures.json file if it doesn't exist
#             open(path, "w").close()
#
#         with open(path, "r+") as f:  # placing 'w+' here will result in race conditions
#             lock_file(f, exclusive=True)
#             try:
#                 json.dump(self.signatures, f, indent=4, sort_keys=True)
#             finally:
#                 unlock_file(f)
#
#         return self
#
#     def get(self, sighash, timeout=2):
#         """
#         get a function signature for a sighash
#         1) try local cache
#         2) try online lookup (if enabled; if not flagged as unavailable)
#         :param sighash: function signature hash as hexstr
#         :param timeout: online lookup timeout
#         :return: list of matching function signatures
#         """
#         if not sighash.startswith("0x"):
#             sighash = "0x%s" % sighash  # normalize sighash format
#         if (
#             self.enable_online_lookup
#             and not self.signatures.get(sighash)
#             and sighash not in self.online_lookup_miss
#             and time.time() > self.online_directory_unavailable_until
#         ):
#             # online lookup enabled, and signature not in cache, sighash was not a miss earlier, and online directory not down
#             logging.debug(
#                 "Signatures: performing online lookup for sighash %r" % sighash
#             )
#             try:
#                 funcsigs = SignatureDb.lookup_online(
#                     sighash, timeout=timeout
#                 )  # might return multiple sigs
#                 if funcsigs:
#                     # only store if we get at least one result
#                     self.update_signatures({sighash: funcsigs})
#                 else:
#                     # miss
#                     self.online_lookup_miss.add(sighash)
#             except FourByteDirectoryOnlineLookupError as fbdole:
#                 self.online_directory_unavailable_until = (
#                     time.time() + 2 * 60
#                 )  # wait at least 2 mins to try again
#                 logging.warning(
#                     "online function signature lookup not available. will not try to lookup hash for the next 2 minutes. exception: %r"
#                     % fbdole
#                 )
#
#         if sighash not in self.signatures:
#             return []
#         if type(self.signatures[sighash]) != list:
#             return [self.signatures[sighash]]
#         return self.signatures[sighash]
#
#     def __getitem__(self, item):
#         """
#         Provide dict interface Signatures()[sighash]
#         :param item: sighash
#         :return: list of matching signatures
#         """
#         return self.get(sighash=item)
#
#     def import_from_solidity_source(
#         self, file_path, solc_binary="solc", solc_args=None
#     ):
#         """
#         Import Function Signatures from solidity source files
#         :param file_path: solidity source code file path
#         :return: self
#         """
#         self.update_signatures(
#             self.get_sigs_from_file(
#                 file_path, solc_binary=solc_binary, solc_args=solc_args
#             )
#         )
#         return self
#
#     @staticmethod
#     def lookup_online(sighash, timeout=None, proxies=None):
#         """
#         Lookup function signatures from 4byte.directory.
#         //tintinweb: the smart-contract-sanctuary project dumps contracts from etherscan.io and feeds them into
#                      4bytes.directory.
#                      https://github.com/tintinweb/smart-contract-sanctuary
#
#         :param sighash: function signature hash as hexstr
#         :param timeout: optional timeout for online lookup
#         :param proxies: optional proxy servers for online lookup
#         :return: a list of matching function signatures for this hash
#         """
#         if not ethereum_input_decoder:
#             return None
#         return list(
#             ethereum_input_decoder.decoder.FourByteDirectory.lookup_signatures(
#                 sighash, timeout=timeout, proxies=proxies
#             )
#         )
#
#     @staticmethod
#     def get_sigs_from_file(file_name, solc_binary="solc", solc_args=None):
#         """
#         :param file_name: accepts a filename
#         :return: their signature mappings
#         """
#         sigs = {}
#         cmd = [solc_binary, "--hashes", file_name]
#         if solc_args:
#             cmd.extend(solc_args.split())
#         try:
#             p = Popen(cmd, stdout=PIPE, stderr=PIPE)
#             stdout, stderr = p.communicate()
#             ret = p.returncode
#
#             if ret != 0:
#                 raise CompilerError(
#                     "Solc experienced a fatal error (code %d).\n\n%s"
#                     % (ret, stderr.decode("UTF-8"))
#                 )
#         except FileNotFoundError:
#             raise CompilerError(
#                 "Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable."
#             )
#         stdout = stdout.decode("unicode_escape").split("\n")
#         for line in stdout:
#             if (
#                 "(" in line and ")" in line and ":" in line
#             ):  # the ':' need not be checked but just to be sure
#                 sigs["0x" + line.split(":")[0]] = [line.split(":")[1].strip()]
#         logging.debug("Signatures: found %d signatures after parsing" % len(sigs))
#         return sigs
