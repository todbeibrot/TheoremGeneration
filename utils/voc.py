from pathlib import Path
from utils.storage import version_name, latest_version, latest_version_path, next_version, next_version_path


# The vocabulary is a mapping from tokens to their representation. During training, each parallel environment will get a copy of the vocabulary.
# We will collect new tokens while training and regularly collect all new tokens from the environments, merge them and update the copys.
class Vocabulary:

    def __init__(self, save_path="", load_path=""):
        self.token_to_id = {"<PAD>": 0, "<UNKNOWN>": 1}
        self.next_id = 2
        root = Path(__file__).resolve().parents[1]
        if save_path:
            self.save_path = save_path
        else:
            self.save_path = root / "data" / "vocabularys"
        if load_path:
            self.load(load_path)
        self.save()

    def merge_tokens(self, tokens):
        """
        tokens: iterable[str]
        """
        new_tokens = set()
        for token in tokens:
            if token not in self.token_to_id:
                new_tokens.add(token)
                self.token_to_id[token] = self.next_id
                self.next_id += 1
        self.save_new_tokens(tokens)


    def get_mapping(self):
        return self.token_to_id.copy()

    def save_new_tokens(self, tokens):
        with open(self.get_save_path(), "a", encoding="utf-8") as f:
            for token in tokens:
                f.write(token + "\n")

    def save(self, path=""):
        save_path = self.get_save_path(path, True)
        with open(save_path , "w", encoding="utf-8") as f:
            for key in self.token_to_id:
                f.write(key + "\n")

    def load(self, path=""):
        load_path = self.get_save_path(path)
        if load_path:
            self.token_to_id = {}
            with open(load_path, "r", encoding="utf-8") as f:
                for i, line in enumerate(f):
                    key = line.rstrip("\n")
                    self.token_to_id[key] = i

    def get_save_path(self, path="", next=False):
        path = path if path else self.save_path
        if next:
            return next_version_path("voc", path, "txt")
        return latest_version_path("voc", path, "txt")


# The vocabulary is a mapping from tokens to their representation. During training, each parallel environment will get a copy of the vocabulary.
# We will collect new tokens while training and regularly collect all new tokens from the environments, merge them and update the copys.
def merge_worker_vocabularies(vocab: Vocabulary, workers):
    collected = set()
    for w in workers:
        collected |= w.consume_new_tokens()
    vocab.merge_tokens(collected)
    mapping = vocab.get_mapping()
    for w in workers:
        w.vocabulary(mapping)