import traceback


def is_prehook() -> bool:
    """Check if we are in prehook.  One of Bernhard's trademark hacks!"""
    return "pre_hook" in traceback.format_stack()[-5]
