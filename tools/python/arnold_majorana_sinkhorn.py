import itertools
import torch
import torch.nn as nn


class ArnoldCohenRegularizationLoss(nn.Module):

    def __init__(self, eps=1e-8):
        super().__init__()
        self.eps = eps

    def compute_basis_ac_loss(self, Gamma):
        """Computes Arnold-Cohen 3-term identity loss for a basis matrix Gamma.

        Args:
            Gamma: (d_in, d_E) Basis matrix (e.g. gamma_real or gamma_dual)

        Returns:
            ac_loss: Scalar Frobenius norm penalty enforcing the Arnold-Cohen
            relation
        """
        d_in, d_E = Gamma.shape
        if d_in < 3:
            return torch.tensor(0.0, device=Gamma.device, dtype=Gamma.dtype)

        # 1. Compute Pairwise Bivectors W_ij = gamma_i (x) gamma_j - gamma_j (x) gamma_i
        # Shape: (d_in, d_in, d_E, d_E)
        gamma_i = Gamma.unsqueeze(1).unsqueeze(-1)  # (d_in, 1, d_E, 1)
        gamma_j = Gamma.unsqueeze(0).unsqueeze(-2)  # (1, d_in, 1, d_E)

        W = torch.matmul(gamma_i, gamma_j) - torch.matmul(
            gamma_j.transpose(-1, -2), gamma_i.transpose(-1, -2)
        )

        # 2. Extract Triplet Indices (i < j < k)
        triplets = list(itertools.combinations(range(d_in), 3))
        loss_ac = 0.0

        for i, j, k in triplets:
            W_ij = W[i, j]  # (d_E, d_E)
            W_jk = W[j, k]  # (d_E, d_E)
            W_ki = W[k, i]  # (d_E, d_E)

            # 3-term Arnold-Cohen Identity: W_ij*W_jk + W_jk*W_ki + W_ki*W_ij
            R_ijk = (
                torch.matmul(W_ij, W_jk)
                + torch.matmul(W_jk, W_ki)
                + torch.matmul(W_ki, W_ij)
            )

            loss_ac = loss_ac + torch.sum(R_ijk**2)

        # Normalize by number of triplets
        num_triplets = max(len(triplets), 1)
        return loss_ac / num_triplets

    def forward(self, gamma_real, gamma_dual):
        """Computes joint Arnold-Cohen regularization across real and dual Clifford bases."""
        loss_real = self.compute_basis_ac_loss(gamma_real)
        loss_dual = self.compute_basis_ac_loss(gamma_dual)
        return loss_real + loss_dual


class ArnoldMajoranaNetwork(nn.Module):
    def __init__(self, in_features, num_components, carrier_dim=8):
        super().__init__()
        self.K = num_components
        self.carrier_dim = carrier_dim
        # Placeholders for basis
        self.gamma_real = nn.Parameter(torch.randn(in_features, carrier_dim))
        self.gamma_dual = nn.Parameter(torch.randn(in_features, carrier_dim))

    def forward(self, X):
        # Dummy forward pass for demonstration
        M = X.shape[0]
        S = torch.ones(M, self.K, device=X.device, dtype=X.dtype)
        E_arnold = torch.zeros(M, self.K, device=X.device, dtype=X.dtype)
        return S, E_arnold

def compute_arnold_poisson_cost(N, S, b, E_arnold):
    # Dummy cost matrix computation
    M = N.shape[0]
    K = S.shape[1]
    return torch.rand(M, K, device=N.device, dtype=N.dtype)


class ArnoldMajoranaSinkhornPipeline(nn.Module):

    def __init__(
        self,
        in_features,
        num_components,
        epsilon=0.05,
        tau_1=0.5,
        tau_2=0.5,
        max_iter=30,
        lambda_ac=0.1,  # Weight for Arnold-Cohen Loss
    ):
        super().__init__()
        self.arnold_net = ArnoldMajoranaNetwork(
            in_features, num_components, carrier_dim=8
        )
        self.epsilon = epsilon
        self.alpha_1 = tau_1 / (tau_1 + epsilon)
        self.alpha_2 = tau_2 / (tau_2 + epsilon)
        self.max_iter = max_iter
        self.lambda_ac = lambda_ac

        # Arnold-Cohen Loss Module
        self.ac_loss_fn = ArnoldCohenRegularizationLoss()

    def forward(self, X, N, b):
        M, K = X.shape[0], self.arnold_net.K

        # Step 1: Forward pass through Arnold-Majorana Network
        S, E_arnold = self.arnold_net(X)

        # Step 2: Compute Arnold-Cohen Basis Regularization Loss
        loss_ac = self.ac_loss_fn(
            self.arnold_net.gamma_real, self.arnold_net.gamma_dual
        )

        # Step 3: Construct Cost Matrix C_ik
        C = compute_arnold_poisson_cost(N, S, b, E_arnold)

        # Step 4: Unbalanced Sinkhorn Loop (Damped Log-Domain)
        r = (N / (N.sum() + 1e-12)).squeeze(-1)
        c = torch.full((K,), 1.0 / K, device=X.device, dtype=X.dtype)

        log_r = torch.log(r + 1e-12)
        log_c = torch.log(c + 1e-12)

        f = torch.zeros(M, device=X.device, dtype=X.dtype)
        g = torch.zeros(K, device=X.device, dtype=X.dtype)

        for _ in range(self.max_iter):
            M_f = (g.unsqueeze(0) - C) / self.epsilon
            f = self.alpha_1 * (
                self.epsilon * log_r - self.epsilon * torch.logsumexp(M_f, dim=1)
            )

            M_g = (f.unsqueeze(1) - C) / self.epsilon
            g = self.alpha_2 * (
                self.epsilon * log_c - self.epsilon * torch.logsumexp(M_g, dim=0)
            )

        log_P = (f.unsqueeze(1) + g.unsqueeze(0) - C) / self.epsilon
        P = torch.exp(log_P)

        # Total Loss combines Sinkhorn OT Cost + Arnold-Cohen Regularization
        ot_loss = torch.sum(P * C)
        total_loss = ot_loss + self.lambda_ac * loss_ac

        return P, total_loss, ot_loss, loss_ac


if __name__ == "__main__":
    # --- Training Verification Script ---
    torch.manual_seed(42)

    M = 40  # 40 observation points
    in_features = 4  # 4 input dimensions (4 choose 3 = 4 triplets)
    K = 3  # 3 expert components

    X = torch.randn(M, in_features)
    b = 1.0 * torch.ones(M, 1)
    N = torch.poisson(8.0 * torch.exp(-torch.norm(X, dim=-1, keepdim=True)) + b)

    pipeline = ArnoldMajoranaSinkhornPipeline(
        in_features, K, epsilon=0.05, lambda_ac=0.5
    )
    optimizer = torch.optim.Adam(pipeline.parameters(), lr=0.02)

    print("Training with Arnold-Cohen Regularization:\n")
    for step in range(1, 26):
        optimizer.zero_grad()
        P, total_loss, ot_loss, loss_ac = pipeline(X, N, b)
        total_loss.backward()
        optimizer.step()

        if step % 5 == 0 or step == 1:
            print(
                f"Step {step:2d} | Total Loss: {total_loss.item():8.2f} | "
                f"OT Loss: {ot_loss.item():8.2f} | "
                f"AC Loss: {loss_ac.item():8.6f}"
            )
