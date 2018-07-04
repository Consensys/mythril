#!/usr/bin/env python3
# -*- coding: UTF-8 -*-
"""mythril.py: Function Signature Database
"""
import re
import os
import json
import time
import pathlib
import logging
from ethereum import utils

# todo: tintinweb - make this a normal requirement? (deps: eth-abi and requests, both already required by mythril)
try:
    # load if available but do not fail
    import ethereum_input_decoder
    from ethereum_input_decoder.decoder import FourByteDirectoryOnlineLookupError
except ImportError:
    # fake it :)
    ethereum_input_decoder = None
    FourByteDirectoryOnlineLookupError = Exception


class SimpleFileLock(object):
    # todo: replace with something more reliable. this is a quick shot on concurrency and might not work in all cases

    def __init__(self, path):
        self.path = path
        self.lockfile = pathlib.Path("%s.lck" % path)
        self.locked = False

    def aquire(self, timeout=5):
        if self.locked:
            raise Exception("SimpleFileLock: lock already aquired")

        t_end = time.time()+timeout
        while time.time() < t_end:
            # try to aquire lock
            try:
                self.lockfile.touch(mode=0o0000, exist_ok=False)  # touch the lockfile
                # lockfile does not exist. we have a lock now
                self.locked = True
                return
            except FileExistsError as fee:
                # check if lockfile date exceeds age and cleanup lock
                if time.time() > self.lockfile.stat().st_mtime + 60 * 5:
                    self.release(force=True)  # cleanup old lockfile > 5mins

                time.sleep(0.5)  # busywait is evil
                continue

        raise Exception("SimpleFileLock: timeout hit. failed to aquire lock: %s"% (time.time()-self.lockfile.stat().st_mtime))

    def release(self, force=False):
        if not force and not self.locked:
            raise Exception("SimpleFileLock: aquire lock first")

        try:
            self.lockfile.unlink()  # might throw if we force unlock and the file gets removed in the meantime. TOCTOU
        except FileNotFoundError as fnfe:
            logging.warning("SimpleFileLock: release(force=%s) on unavailable file. race? %r" % (force, fnfe))

        self.locked = False



class SignatureDb(object):

    def __init__(self, enable_online_lookup=True):
        """
        Constr
        :param enable_online_lookup: enable onlien signature hash lookup
        """
        self.signatures = {}  # signatures in-mem cache
        self.signatures_file = None
        self.signatures_file_lock = None
        self.enable_online_lookup = enable_online_lookup  # enable online funcsig resolving
        self.online_lookup_miss = set()  # temporarily track misses from onlinedb to avoid requesting the same non-existent sighash multiple times
        self.online_directory_unavailable_until = 0  # flag the online directory as unavailable for some time

    def open(self, path=None):
        """
        Open a function signature db from json file

        :param path: specific path to signatures.json; default mythril location if not specified
        :return: self
        """
        if not path:
            #  try default locations
            try:
                mythril_dir = os.environ['MYTHRIL_DIR']
            except KeyError:
                mythril_dir = os.path.join(os.path.expanduser('~'), ".mythril")
            path = os.path.join(mythril_dir, 'signatures.json')

        self.signatures_file = path  # store early to allow error handling to access the place we tried to load the file

        if not os.path.exists(path):
            logging.debug("Signatures: file not found: %s" % path)
            raise FileNotFoundError("Missing function signature file. Resolving of function names disabled.")

        self.signatures_file_lock = SimpleFileLock(self.signatures_file)  # lock file to prevent concurrency issues
        self.signatures_file_lock.aquire()  # try to aquire it within the next 10s

        with open(path, 'r') as f:
            sigs = json.load(f)

        self.signatures_file_lock.release()  # release lock

        # normalize it to {sighash:list(signatures,...)}
        for sighash, funcsig in sigs.items():
            if isinstance(funcsig, list):
                self.signatures = sigs  # keep original todo: tintinweb - super hacky. make sure signatures.json is initially in correct format fixme
                break  # already normalized
            self.signatures.setdefault(sighash, [])
            self.signatures[sighash].append(funcsig)

        return self

    def write(self, path=None, sync=True):
        """
        Write signatures database as json to file

        :param path: specify path otherwise update the file that was loaded with open()
        :param sync: lock signature file, load contents and merge it into memcached sighash db, then save it
        :return: self
        """
        path = path or self.signatures_file
        self.signatures_file_lock = SimpleFileLock(path)  # lock file to prevent concurrency issues
        self.signatures_file_lock.aquire()  # try to aquire it within the next 10s

        if sync and os.path.exists(path):
            # reload and save if file exists
            with open(path, 'r') as f:
                sigs = json.load(f)

            sigs.update(self.signatures)  # reload file and merge cached sigs into what we load from file
            self.signatures = sigs

        with open(path, 'w') as f:
            json.dump(self.signatures, f)

        self.signatures_file_lock.release()
        return self

    def get(self, sighash, timeout=2):
        """
        get a function signature for a sighash
        1) try local cache
        2) try online lookup (if enabled; if not flagged as unavailable)
        :param sighash: function signature hash as hexstr
        :param timeout: online lookup timeout
        :return: list of matching function signatures
        """
        if not sighash.startswith("0x"):
            sighash = "0x%s" % sighash  # normalize sighash format

        if self.enable_online_lookup and not self.signatures.get(sighash) and sighash not in self.online_lookup_miss and time.time() > self.online_directory_unavailable_until:
            # online lookup enabled, and signature not in cache, sighash was not a miss earlier, and online directory not down
            logging.debug("Signatures: performing online lookup for sighash %r" % sighash)
            try:
                funcsigs = SignatureDb.lookup_online(sighash, timeout=timeout)  # might return multiple sigs
                if funcsigs:
                    # only store if we get at least one result
                    self.signatures[sighash] = funcsigs
                else:
                    # miss
                    self.online_lookup_miss.add(sighash)
            except FourByteDirectoryOnlineLookupError as fbdole:
                self.online_directory_unavailable_until = time.time() + 2 * 60  # wait at least 2 mins to try again
                logging.warning("online function signature lookup not available. will not try to lookup hash for the next 2 minutes. exception: %r" % fbdole)
        return self.signatures[sighash]  # raise keyerror

    def __getitem__(self, item):
        """
        Provide dict interface Signatures()[sighash]
        :param item: sighash
        :return: list of matching signatures
        """
        return self.get(sighash=item)

    def import_from_solidity_source(self, code):
        """
        Import Function Signatures from solidity source files
        :param code: solidity source code
        :return: self
        """
        self.signatures.update(SignatureDb.parse_function_signatures_from_solidity_source(code))
        return self

    @staticmethod
    def lookup_online(sighash, timeout=None, proxies=None):
        """
        Lookup function signatures from 4byte.directory.
        //tintinweb: the smart-contract-sanctuary project dumps contracts from etherscan.io and feeds them into
                     4bytes.directory.
                     https://github.com/tintinweb/smart-contract-sanctuary

        :param sighash: function signature hash as hexstr
        :param timeout: optional timeout for online lookup
        :param proxies: optional proxy servers for online lookup
        :return: a list of matching function signatures for this hash
        """
        if not ethereum_input_decoder:
            return None
        return list(ethereum_input_decoder.decoder.FourByteDirectory.lookup_signatures(sighash,
                                                                                       timeout=timeout,
                                                                                       proxies=proxies))

    @staticmethod
    def parse_function_signatures_from_solidity_source(code):
        """
        Parse solidity sourcecode for function signatures and return the signature hash and function signature
        :param code: solidity source code
        :return: dictionary {sighash: function_signature}
        """
        sigs = {}

        funcs = re.findall(r'function[\s]+(.*?\))', code, re.DOTALL)
        for f in funcs:
            f = re.sub(r'[\n]', '', f)
            m = re.search(r'^([A-Za-z0-9_]+)', f)

            if m:
                signature = m.group(1)
                m = re.search(r'\((.*)\)', f)
                _args = m.group(1).split(",")
                types = []

                for arg in _args:
                    _type = arg.lstrip().split(" ")[0]

                    if _type == "uint":
                        _type = "uint256"

                    types.append(_type)

                typelist = ",".join(types)
                signature += "(" + typelist + ")"
                signature = re.sub(r'\s', '', signature)
                sigs["0x" + utils.sha3(signature)[:4].hex()] = signature

        logging.debug("Signatures: parse soldiity found %d signatures" % len(sigs))
        return sigs
