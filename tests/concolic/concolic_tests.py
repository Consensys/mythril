import pytest

test_data = (
    (, ),
)


@pytest.mark.parametrize("inputs,output", test_data)
def test_sar(inputs, output):
    # Arrange
    state = get_state()

    state.mstate.stack = inputs
    instruction = Instruction("sar", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert simplify(new_state.mstate.stack[-1]) == output
