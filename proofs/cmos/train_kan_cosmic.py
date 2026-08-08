import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np

try:
    from kan import KANLayer
except ImportError:
    pass

from RecurrentExpertKAN import RecurrentExpertKAN

def generate_cosmic_ray_sequence(batch_size=32, seq_len=10, in_dim=4):
    """
    Generates synthetic CMOS pixel patches over time.
    Cosmic rays are huge impulses on 1 or 2 pixels in random frames.
    """
    # Background read noise + shot noise
    X = torch.poisson(torch.ones(batch_size, seq_len, in_dim) * 100.0) + torch.randn(batch_size, seq_len, in_dim) * 5.0
    
    labels = torch.zeros(batch_size, seq_len, 1)
    
    # Inject cosmic rays
    for b in range(batch_size):
        # 50% chance to have a cosmic ray in this sequence
        if np.random.rand() > 0.5:
            t_cr = np.random.randint(1, seq_len)
            pixel_idx = np.random.randint(0, in_dim)
            X[b, t_cr, pixel_idx] += np.random.uniform(1000, 5000)
            labels[b, t_cr, 0] = 1.0 # True if cosmic ray detected
            
    # Normalize inputs somewhat
    X = X / 100.0
    return X, labels

def train_model(model, X_train, y_train, epochs=50):
    optimizer = optim.Adam(model.parameters(), lr=0.01)
    # BCE loss for cosmic ray detection
    criterion = nn.BCEWithLogitsLoss()
    
    for epoch in range(epochs):
        optimizer.zero_grad()
        out = model(X_train) # (batch, seq_len, out_dim)
        loss = criterion(out, y_train)
        loss.backward()
        optimizer.step()
        
        if epoch % 10 == 0:
            print(f"Epoch {epoch}: Loss = {loss.item():.4f}")

if __name__ == "__main__":
    # Generate simple training data
    torch.manual_seed(42)
    np.random.seed(42)
    
    X, y = generate_cosmic_ray_sequence(100, 10, 4)
    print("Training RecurrentExpertKAN...")
    
    model = RecurrentExpertKAN(in_dim=4, hidden_dim=8, out_dim=1, layers=2)
    
    train_model(model, X, y, epochs=100)
    print("Training complete!")
    
    # Test pass
    model.eval()
    with torch.no_grad():
        test_X, test_y = generate_cosmic_ray_sequence(1, 10, 4)
        out = model(test_X)
        probs = torch.sigmoid(out)
        print("\nTest Sequence Predictions vs Labels:")
        print("Probs:", np.round(probs[0].squeeze().numpy(), 3))
        print("Labels:", test_y[0].squeeze().numpy())
