import signal
from types import FrameType
from mythril.exceptions import OutOfTimeError


def sigalrm_handler(signum: int, frame: FrameType) -> None:
    raise OutOfTimeError


def start_timeout(timeout: int) -> None:
    """
    Starts a timeout
    :param timeout: Time in seconds to set the timeout for
    :return: None
    """
    signal.signal(signal.SIGALRM, sigalrm_handler)
    signal.alarm(timeout)


def disable_timeout() -> None:
    """
    Ensures that the timeout is disabled
    :return: None
    """
    signal.alarm(0)
