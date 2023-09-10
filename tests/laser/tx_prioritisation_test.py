import pytest
import numpy as np
from mythril.laser.ethereum.tx_prioritiser import RfTxPrioritiser
from unittest.mock import Mock, patch, mock_open


def mock_predict_proba(X):
    if X[0][-1] == 1:
        return np.array([[0.1, 0.7, 0.1, 0.1]])
    elif X[0][-1] == 2:
        return np.array([[0.1, 0.1, 0.7, 0.1]])
    else:
        return np.array([[0.1, 0.1, 0.1, 0.7]])


class MockSolidityContract:
    def __init__(self, features):
        self.features = features


@pytest.fixture
def rftp_instance():
    contract = MockSolidityContract(
        features={"function1": {"feature1": 1, "feature2": 2}}
    )

    with patch("pickle.load") as mock_pickle_load, patch("builtins.open", mock_open()):
        mock_model = Mock()
        mock_model.predict_proba = mock_predict_proba
        mock_pickle_load.return_value = mock_model

        rftp = RfTxPrioritiser(contract=contract, model_path="path/to/mock/model.pkl")

    return rftp


def test_preprocess_features(rftp_instance):
    expected_features = np.array([[1, 2]])
    assert np.array_equal(rftp_instance.preprocessed_features, expected_features)


@pytest.mark.parametrize(
    "address,previous_predictions,expected_sequence",
    [
        (1, [], [2, 2, 2]),
        (2, [], [2, 2, 2]),
        (1, [0], [3, 3, 3]),
        (2, [1], [1, 1, 1]),
        (3, [1, 2], [2, 2, 2]),
        (1, [0, 2, 5], [3, 3, 3]),
    ],
)
def test_next_method(rftp_instance, address, previous_predictions, expected_sequence):
    rftp_instance.recent_predictions = previous_predictions
    predictions_sequence = rftp_instance.__next__(address=address)

    assert len(predictions_sequence) == 3
    assert predictions_sequence == expected_sequence
