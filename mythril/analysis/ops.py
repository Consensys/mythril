class Call:

    def __init__(self, block_uid, addr, call_type, to, value):
        self.block_uid = block_uid
        self.addr = addr
        self.to = to
        self.call_type = call_type
        self.value = value

    class SStore:
        def __init__(self, block_uid, addr, index, value):
            self.index = index
            self.value = value

    class SLoad:
        def __init__(self, index, value):
            self.index = index
            self.value = value
