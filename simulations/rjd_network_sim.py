import numpy as np


def simulate_observer_projection(N: int, steps: int = 2500, dim: int = 3, seed: int = 42):
    """Simulates discrete RJD updates in a d-dimensional observer interface."""
    rng = np.random.default_rng(seed)
    a = rng.normal(0.0, 1.0, size=(N, dim))

    jerk_history = []
    radius_history = []

    for _ in range(steps):
        diff = a[np.newaxis, :, :] - a[:, np.newaxis, :]
        dist = np.linalg.norm(diff, axis=-1, keepdims=True)

        valid = dist > 1e-12
        safe_dist = np.where(valid, dist, 1.0)
        unit_vectors = np.where(valid, diff / safe_dist, 0.0)

        J = np.sum(unit_vectors, axis=1)
        a = a + J

        barycenter = np.mean(a, axis=0, keepdims=True)
        radius_history.append(np.mean(np.linalg.norm(a - barycenter, axis=-1)))
        jerk_history.append(np.mean(np.linalg.norm(J, axis=-1)))

    mean_J = float(np.mean(jerk_history[-500:]))
    std_J = float(np.std(jerk_history[-500:]))
    mean_R = float(np.mean(radius_history[-500:]))
    return mean_J, std_J, mean_R, mean_J / N, mean_J / mean_R


def simulate_coordinate_free_graph(N: int = 32, steps: int = 1500, eta: float = 0.1, seed: int = 42):
    """Simulates coordinate-free antisymmetric relational matrix R_{ik}."""
    rng = np.random.default_rng(seed)
    R = rng.normal(0.0, 1.0, size=(N, N))
    R = 0.5 * (R - R.T)
    np.fill_diagonal(R, 0.0)

    for _ in range(steps):
        diff = R[:, :, np.newaxis] - R[np.newaxis, :, :]
        J_rel = np.mean(np.sign(diff), axis=2)
        J_rel = 0.5 * (J_rel - J_rel.T)
        R = R + eta * J_rel

    W = 1.0 / (np.abs(R) + 0.1)
    np.fill_diagonal(W, 0.0)
    deg = np.sum(W, axis=1)
    D_inv_sqrt = np.diag(1.0 / np.sqrt(deg))
    L_norm = np.eye(N) - (D_inv_sqrt @ W @ D_inv_sqrt)
    return np.linalg.eigvalsh(L_norm)


if __name__ == "__main__":
    print("=== 1. OBSERVER INTERFACE SCALING VERIFICATION (d=3) ===")
    for n in:
        mJ, sJ, mR, j_n, j_r = simulate_observer_projection(n)
        print(f"N={n:3d} | <J>={mJ:8.4f} | sigma_J={sJ:6.4f} | <J>/N={j_n:6.4f} | <J>/R={j_r:6.4f}")

    print("\n=== 2. COORDINATE-FREE GRAPH LAPLACIAN SPECTRUM ===")
    eigs = simulate_coordinate_free_graph(N=32)
    print(f"Spectral Gap (lambda_2): {eigs:.4f} | Max Eigenvalue (lambda_N): {eigs[-1]:.4f}")
