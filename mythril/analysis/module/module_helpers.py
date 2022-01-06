import traceback


def is_prehook() -> bool:
    """Check if we are in prehook.  One of Bernhard's trademark hacks!
    Let's leave it to this for now, unless we need to check prehook for
    a lot more modules.
    """

    assert ("pre_hook" in traceback.format_stack()[-5]) or (
        "post_hook" in traceback.format_stack()[-5]
    )
    return "pre_hook" in traceback.format_stack()[-5]
