import os
import time
import errno

"""
credits: https://github.com/dmfrey/FileLock
"""


class LockFileException(Exception):
    pass


class LockFile(object):
    """
    Locks files.
    """

    def __init__(self, file_name, timeout=100, delay=0.05):
        """
        Initialises the file locker
        """
        if timeout is not None and delay is None:
            raise ValueError("If timeout is not None, then delay must not be None.")
        self.is_locked = False
        self.lockfile = os.path.join(os.getcwd(), f"{file_name}.lock")
        self.file_name = file_name
        self.timeout = timeout
        self.delay = delay

    def acquire(self):
        """
        Acquires a lock when possible.
        """
        start_time = time.time()
        while True:
            try:
                self.fd = os.open(self.lockfile, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                self.is_locked = True
                break
            except OSError as e:
                if e.errno != errno.EEXIST:
                    raise
                if (time.time() - start_time) >= self.timeout:
                    raise FileLockException(
                        f"Stuck for more than {self.timeout} seconds waiting to unlock the file {self.filename}."
                    )
                time.sleep(self.delay)

    def release(self):
        """
        Releases the lock
        """
        if self.is_locked:
            os.close(self.fd)
            os.unlink(self.lockfile)
            self.is_locked = False

    def __enter__(self):
        """
        Lock gets acquired at the `with` statement.
        """
        if not self.is_locked:
            self.acquire()
        return self

    def __exit__(self, type, value, traceback):
        """
        Lock get's released at the end of the `with` block
        """
        if self.is_locked:
            self.release()

    def __del__(self):
        """
        Releases the lock during deletion.
        """
        self.release()
