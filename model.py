import torch
import torch.nn as nn

from ray.rllib.core.rl_module.torch import TorchRLModule
from ray.rllib.core.rl_module.apis.value_function_api import ValueFunctionAPI
from ray.rllib.core.columns import Columns


class SmallAttentionModule(TorchRLModule, ValueFunctionAPI):

    def setup(self):
        super().setup()
        cfg = self.model_config

        self.vocab_size = cfg.get("vocab_size", 200)
        self.embed_dim = cfg.get("embed_dim", 64)
        self.num_heads = cfg.get("num_heads", 2)
        self.num_layers = cfg.get("num_layers", 1)

        # Embeddings
        self.token_embedding = nn.Embedding(self.vocab_size, self.embed_dim - 1)

        # Transformer
        encoder_layer = nn.TransformerEncoderLayer(
            d_model=self.embed_dim,
            nhead=self.num_heads,
            batch_first=True,
            dim_feedforward=2 * self.embed_dim,
        )
        self.transformer = nn.TransformerEncoder(
            encoder_layer,
            num_layers=self.num_layers
        )

        # Heads
        self.policy_head = nn.Linear(self.embed_dim, self.action_space.n)
        self.value_head = nn.Linear(self.embed_dim, 1)

    def _forward(self, batch, **kwargs):
        obs = batch[Columns.OBS]

        valid_actions = obs["action_mask"]
        obs = obs["observations"]

        x = self._encode(obs)

        logits = self.policy_head(x)
        logits = logits.masked_fill(valid_actions == 0, -1e8)
        
        values = self.value_head(x).squeeze(-1)

        return {
            Columns.ACTION_DIST_INPUTS: logits,
            Columns.VF_PREDS: values,
        }
    
    
    def compute_values(self, batch, embeddings=None):
        obs = batch[Columns.OBS]

        obs = obs["observations"]

        x = self._encode(obs)

        values = self.value_head(x).squeeze(-1)
        return values

    def _encode(self, obs):
        tokens = obs["tokens"].long()
        depths = obs["depths"].unsqueeze(-1)

        tok_emb = self.token_embedding(tokens)
        x = torch.cat([tok_emb, depths], dim=-1)

        x = self.transformer(x)
        x = x.mean(dim=1)

        return x