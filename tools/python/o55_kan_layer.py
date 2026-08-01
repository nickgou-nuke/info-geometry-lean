import torch
import torch.nn as nn
import torch.optim as optim

class O55KANLayer(nn.Module):
    def __init__(self):
        super(O55KANLayer, self).__init__()
        
        # 1. Define the Split-Metric \eta_{(5,5)}
        self.eta = torch.zeros(10, 10)
        self.eta[:5, 5:] = torch.eye(5)
        self.eta[5:, :5] = torch.eye(5)
        self.eta = nn.Parameter(self.eta, requires_grad=False)
        
        # 2. Define the raw trainable parameters
        self.W_raw = nn.Parameter(torch.randn(10, 10) * 0.1)
        
    def get_lie_algebra_element(self):
        # A = W_raw - \eta * W_raw^T * \eta
        return self.W_raw - torch.matmul(self.eta, torch.matmul(self.W_raw.t(), self.eta))
        
    def get_gauge_transformation(self):
        # G = exp(A)
        A = self.get_lie_algebra_element()
        return torch.matrix_exp(A)
        
    def forward(self, x):
        # x is expected to be of shape (batch_size, 10)
        G = self.get_gauge_transformation()
        # Rotate expert states: out = x * G^T  (equivalent to G * x if x is column, here x is row)
        # So x_out = x @ G.t()
        return torch.matmul(x, G.t())
        
    def check_symmetry(self):
        G = self.get_gauge_transformation()
        # Check if G * \eta * G^T = \eta
        metric_out = torch.matmul(G, torch.matmul(self.eta, G.t()))
        diff = torch.max(torch.abs(metric_out - self.eta)).item()
        return diff

def compute_entropy(x, eta):
    # Quadratic form: x^T \eta x. Since x is (batch, 10), we do batched dot product
    # x @ \eta @ x^T -> take diagonal
    return torch.sum(x * torch.matmul(x, eta), dim=1)

def main():
    torch.manual_seed(42)
    
    batch_size = 32
    # Dummy input states Phi(X)
    X_in = torch.randn(batch_size, 10)
    
    # Calculate the exact target entropy from the input, since the transformation 
    # must perfectly preserve it!
    layer = O55KANLayer()
    target_entropy = compute_entropy(X_in, layer.eta)
    
    # We will try to artificially optimize W_raw to minimize some arbitrary loss,
    # just to show that no matter what the optimizer does, the entropy is preserved 
    # and the O(5,5) symmetry holds perfectly.
    
    # Let's say we want to push the outputs to be close to some random target vector
    target_output = torch.randn(batch_size, 10) * 2.0
    
    optimizer = optim.Adam(layer.parameters(), lr=0.01)
    
    print("Starting O(5,5) KAN Layer Optimization...")
    print(f"{'Step':<5} | {'Task Loss':<12} | {'Max Entropy Diff':<20} | {'Symmetry Error ||GηGᵀ - η||':<25}")
    print("-" * 75)
    
    for step in range(50):
        optimizer.zero_grad()
        
        # Forward pass
        X_out = layer(X_in)
        
        # 1. Task Loss (e.g., trying to match some downstream target)
        task_loss = torch.mean((X_out - target_output) ** 2)
        
        # Backward pass
        task_loss.backward()
        optimizer.step()
        
        # 2. Verify Entropy Conservation (det(X) invariance)
        current_entropy = compute_entropy(X_out, layer.eta)
        entropy_diff = torch.max(torch.abs(current_entropy - target_entropy)).item()
        
        # 3. Verify O(5,5) Gauge Symmetry in the kernel
        sym_error = layer.check_symmetry()
        
        if step % 10 == 0 or step == 49:
            print(f"{step:<5} | {task_loss.item():<12.6f} | {entropy_diff:<20.4e} | {sym_error:<25.4e}")
            
    print("-" * 75)
    print("Optimization Complete!")
    print("Conclusion: The PyTorch network successfully trains its internal Lie algebra parameters (A ∈ so(5,5)),")
    print("while strictly preserving the metric GηGᵀ = η and exactly conserving the Radon-Nikodym entropy.")

if __name__ == '__main__':
    main()
