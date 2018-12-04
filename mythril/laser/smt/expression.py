class Expression:
    def __init__(self, raw, annotations=None):
        self.raw = raw
        self._annotations = annotations or []

    @property
    def annotations(self):
        return self._annotations

    def annotate(self, annotation):
        if isinstance(annotation, list):
            self._annotations += annotation
        else:
            self._annotations.append(annotation)
