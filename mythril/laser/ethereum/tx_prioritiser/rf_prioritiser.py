import pickle
from sklearn.ensemble import RandomForestClassifier
import numpy as np
from itertools import chain

import logging

log = logging.getLogger(__name__)


class RfTxPrioritiser:
    def __init__(self, contract, depth=3, model_path=None):
        self.rf_path = None
        self.contract = contract
        self.depth = depth

        with open(model_path, "rb") as file:
            self.model = pickle.load(file)
        if self.contract.features is None:
            log.info(
                "There are no available features. Rf based Tx Prioritisation turned off."
            )
            return None
        self.preprocessed_features = self.preprocess_features(self.contract.features)
        self.recent_predictions = []

    def preprocess_features(self, features_dict):
        flat_features = []
        for function_name, function_features in features_dict.items():
            function_features_values = list(function_features.values())
            flat_features.extend(function_features_values)

        return np.array(flat_features).reshape(1, -1)

    def __next__(self, address):
        predictions_sequence = []
        current_features = np.concatenate(
            [
                self.preprocessed_features,
                np.array(self.recent_predictions).reshape(1, -1),
            ],
            axis=1,
        )

        for i in range(self.depth):
            predictions = self.model.predict_proba(current_features)
            most_likely_next_tx = np.argmax(predictions, axis=1)[0]
            predictions_sequence.append(most_likely_next_tx)
            current_features = np.concatenate(
                [
                    self.preprocessed_features,
                    np.array(
                        self.recent_predictions + predictions_sequence[: i + 1]
                    ).reshape(1, -1),
                ],
                axis=1,
            )

        self.recent_predictions.extend(predictions_sequence)
        while len(self.recent_predictions) > self.depth:
            self.recent_predictions.pop(0)
        return predictions_sequence
