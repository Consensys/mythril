from math import exp
from mythril.exceptions import UnsupportedModeError


def get_timeout(bytecode_length: int, mode: str) -> int:
    """
    Returns a dynamically calculated timeout based on the length of the bytecode string.

    :param bytecode_length: Length of the bytecode: len("0x....")
    :param mode: Preset mode (fast or deep)
    """
    if mode == "fast":
        return int(min(100, 15 * exp(bytecode_length / 6000)))
    elif mode == "deep":
        return int(min(1800, 30 * exp(bytecode_length / 3000)))

    raise UnsupportedModeError
