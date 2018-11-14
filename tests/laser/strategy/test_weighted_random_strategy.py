from mythril.laser.ethereum.state import GlobalState


test_worklist = [
    (
        GlobalState(None, None, None),
        [GlobalState(None, None, None), GlobalState(None, None, None)],
    )
]

def test_random_weighted_strategy(work_list):
