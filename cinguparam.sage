from scipy.special import erfcinv
import math
load("https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py")


def GaussianNoiseWidth(n, security_reduction):
    if security_reduction:
        return 2 * math.sqrt(n)  # Regev
    else:
        return 8 / math.sqrt(2 * pi)  # Peikert

def comp_beta(log2_advantage):
    return math.sqrt(2) * erfcinv(2 ** (log2_advantage))


def fresh_variance(params):  # (n,h, security_reduction)
    return (1 + params["n"] + params["n"]) * (
        GaussianNoiseWidth(params["n"], security_reduction=True) ** 2
    )

def round_up(a, dps):
    m = 10**dps
    return math.ceil(a * m) / m

def comp_alpha(log2_advantage):
    eps = 2 ** log2_advantage
    alpha = math.sqrt(log(1 / eps) / math.pi)
    alpha = round_up(alpha, 3)
    return alpha

def comp_sigma_k(log2_advantage, sigma, q, k):
    sigma_k = comp_alpha(log2_advantage) ** (1-math.sqrt(k))
    sigma_k *= q ** (k-math.sqrt(k))
    sigma_k *= sigma ** (math.sqrt(k))
    sigma_k = math.ceil(sigma_k)
    return sigma_k

class PolynomialSet(object):
    def __init__(self, Hamming_weight, inf_norm):
        self.inf_norm = inf_norm
        self.Hamming_weight = Hamming_weight

    def max_norm2(poly):
        return poly.Hamming_weight * (poly.inf_norm)**2

    def add(self, other):  # return a polynomial set with maximal infinite norm and Hamming weight
        return PolynomialSet(
            self.Hamming_weight + other.Hamming_weight,
            self.inf_norm + other.inf_norm,
        )

    def mult(self, other):
        res = PolynomialSet(
            Hamming_weight = self.Hamming_weight + other.Hamming_weight,
            inf_norm=params["delta"] * self.inf_norm * other.inf_norm,
        )
        if res.Hamming_weight > params["n"]:
            res.Hamming_weight = params["n"]
        return res

class CiphertextSet(object):
    def __init__(self, var, pt):
        self.var = var
        self.pt = pt

    def add(self, other, params):
        res = CiphertextSet(
            var=self.var + other.var,
            pt=PolynomialSet.add(self.pt, other.pt),  # Noise variance after addition
        )
        return res

    def mult_plain(self, p, params):  # hybrid operation between plaintext and ciphertext used in SEAL e.g
        return CiphertextSet(PolynomialSet.max_norm2(p) * self.var, PolynomialSet.mult(self.pt, p))

    def mult(self, other, r, params, relin_version):
        # r = t*r_i = PolynomialSet(n, t*math.sqrt(n)/2 + 2*t -1/2) [Faz19,p.17]
        # we do not use mult_plain to compute Var(r*v)
        # use Var(r * v) = n * Var(r) * Var(v) instead 
        p1 = CiphertextSet.mult_plain(self, other.pt, params)  # m1 * v2
        p2 = CiphertextSet.mult_plain(other, self.pt, params)  # m2 * v1

        r1 = CiphertextSet.mult_plain(
            self, r, params
        )  # Var(r * v1) = n * Var(r) * Var(v1)
        r2 = CiphertextSet.mult_plain(
            other, r, params
        )  # Var(r * v2) = n * Var(r) * Var(v2)
        res1 = CiphertextSet.add(p1, p2, params)
        res2 = CiphertextSet.add(r1, r2, params)

        res = CiphertextSet.add(res1, res2, params)
        res.pt = PolynomialSet.mult(self.pt, other.pt)
        res.pt.inf_norm %= params["t"]
        
        #res.var += (params["q"]%params["t"]) * params["n"] * ((params["t"]-1)**2) * params["t"]*params["h"]/12

        return CiphertextSet.relin(res, relin_version, params)  # relinearisation of the result

    def relin(self, relin_version, params):
        res = self
        if relin_version == 1:

            res.var += (
                params["n"]
                * (params["dbc"] + 1)
                * (params["T"] ** 2 + 2)
                * (GaussianNoiseWidth(params["n"], True)) ** 2
            )
        elif relin_version == 2:
            res.var += (
                params["n"]
                * (params["q"]**2)
                * (comp_sigma_k(log2_advantage, GaussianNoiseWidth(params["n"], True), params["q"], 4))**2
                / (12 * params["q"]**6)
            )
        return res

# update w/ new params
def update(params, L):
    params["delta"] = params["n"]
    params["sigma"] = GaussianNoiseWidth(params["n"], True)
    r = PolynomialSet(Hamming_weight=params["n"], inf_norm= params["delta"]*params["t"]/2)  #math.sqrt((1+params["h"])/12) * params["t"])

    pt = PolynomialSet(Hamming_weight=params["n"], inf_norm=params["t"] - 1)
    ct = CiphertextSet(fresh_variance(params), pt)
    ct = mult_many_naif(ct, L, r, params)

    return ct


# ct_f=FV.Mult(ct_1,FV.Mult(ct_2,FV.Mult(...,FV.Mult(ct_k,ct_k+1))))
# this version of multiplication is only for comparing our parameters with Cinguparam
# L is the multiplicative depth of ther complete binary tree
def mult_many_naif(ct, L, r, params):

    res = ct
    for i in range(L):
        res = CiphertextSet.mult(res, res, r, params, relin_version)
    return res


# Generate a set of params for L mults then check correctness and security level using albrecht's primal_usvp(LWE-Estimator)

def gen_params(
    ct, method, min_secu_level, security_reduction, reduction_cost_model, prv_key_distr
):

    if method == "min_modulus":
        n = params["n"]
        first_pass = True
        while first_pass or (estimated_secu_level < min_secu_level):
            first_pass = False
            noise_Gaussian_width = GaussianNoiseWidth(n, security_reduction)
            ct = update(params, L)
            q = MinCorrectModulus(n, ct)
            noise_rate = noise_Gaussian_width / RR(q)
            params["dbc"] = floor(log(q, params["T"]), bits=1000)
            nr_samples = (params["dbc"] + 2) * n
            estimated_secu_level = SecurityLevel(
                n, q, noise_rate, nr_samples, reduction_cost_model, prv_key_distr
            )
            print(
                "Noise variance after a perfect binary tree of mult depth L, with n=", n
            )
            print(ct.var)
            n <<= 1
            params["q"] = q
            params["n"] = n
            
        n >>= 1
        params["n"] = n
        params["delta"] = n
    elif method == "min_degree":
        q = params["q"]
        first_pass = True
        while first_pass or (max_circuit_noise >= max_correctness_noise):
            first_pass = False
            n, estimated_secu_level, noise_rate = MinSecureDegree(
                q,
                min_secu_level,
                prv_key_distr,
                reduction_cost_model,
                security_reduction,
            )
            params["dbc"] = floor(log(q, params["T"]), bits=1000)
            noise_Gaussian_width = GaussianNoiseWidth(n, security_reduction)
            noise_rate = noise_Gaussian_width / RR(q)
            params["sigma"] = noise_rate * q
            q <<= 1
            params["n"] = n
            params["q"] = q
            params["delta"] = params["n"]
            ct = update(params, L)
            print(log(q, 2))
            print(ct.var)
            print(n)
            max_correctness_noise = ((q / params["t"]) * (1 + params["t"]) - q) / 2
            max_circuit_noise = comp_beta(log2_advantage) * math.sqrt(ct.var)
        params["q"] = q
    nr_samples = (params["dbc"] + 2) * n
    return n, estimated_secu_level, log(q, 2), noise_rate, nr_samples, update(params, L).var

# minimal ciphertext space modulus for correctness
def MinCorrectModulus(n, ct):
    first_pass = True
    q = params["q"]
    params["n"] = n
    while first_pass or (max_circuit_noise >= max_correctness_noise):
        first_pass = False
        params["q"] = q
        ct = update(params, L)
        max_correctness_noise = ((q / params["t"]) * (1 + params["t"]) - q) / 2
        max_circuit_noise = comp_beta(log2_advantage) * math.sqrt(ct.var)
        q <<= 1
    params["q"] = q
    return q


# security level
def SecurityLevel(n, q, noise_rate, nr_samples, reduction_cost_model, prv_key_distr):
    ring_operations = primal_usvp(
        n,
        noise_rate,
        q,
        prv_key_distr,
        m=nr_samples,
        success_probability=0.99,
        reduction_cost_model=reduction_cost_model,
    )["rop"]
    secu_level = floor(log(ring_operations) / log(2))
    return secu_level


# minimal degree n for security
def MinSecureDegree(
    q, min_secu_level, prv_key_distr, reduction_cost_model, security_reduction
):
    n = 2048
    first_pass = True
    while first_pass or (estimated_secu_level < min_secu_level):
        first_pass = False
        noise_rate = GaussianNoiseWidth(n, security_reduction) / RR(q)
        params["dbc"] = floor(log(q, params["T"]), bits=1000)
        nr_samples = (params["dbc"] + 2) * n
        estimated_secu_level = SecurityLevel(
            n,
            q,
            noise_rate,
            nr_samples,
            reduction_cost_model,
            prv_key_distr=prv_key_distr,
        )
        n <<= 1
    n >>= 1
    params["n"] = n
    params["delta"] = params["n"]
    return n, estimated_secu_level, noise_rate


# Initial parameters
params = {
    "n": 2048,
    "t": 2,
    "q": 2 ** 30,
    "T": 2 ** 32,  # relin v1
    "alpha": 3.758 # relin v2
}
params["dbc"] = floor(
    log(params["q"], params["T"])
)  # decomp. bit count relinearisation v1 [FV12]
params["delta"] = params["n"]  # expansion factor
params["h"] = 63  #  2 * n / 3 # if h is not fixed
params["sigma"] = GaussianNoiseWidth(params["n"], True)
L = 4
relin_version = 2
noise_rate = GaussianNoiseWidth(params["n"], True) / RR(params["q"])
nr_samples = (params["dbc"] + 2) * params["n"]
prv_key_distr = ((0, 1), 63)
min_secu_level = 110
reduction_cost_model = BKZ.sieve #partial(BKZ.ADPS16, mode="paranoid")
log2_advantage = -64

print("Circuit: perfect binary tree")
print("Exponentiation: x^{L+1}")
print("Cingulata with h=63")
print("Relinearisation", relin_version)
print("Method = min_modulus")
print("L = ", L)

# CinguParam further parameters

pt = PolynomialSet(Hamming_weight=params["n"], inf_norm=params["t"] - 1)
ct = CiphertextSet(fresh_variance(params), pt)

# polynomial r = c0 + c1 * s div q, with ct=(c0,c1) and private key s.
r = PolynomialSet(Hamming_weight=params["n"], inf_norm= params["delta"]*params["t"]/2)  #math.sqrt((1+params["h"])/12) * params["t"])
max_correctness_noise = ((params["q"] / params["t"]) * (1 + params["t"]) - params["q"]) / 2
max_circuit_noise = comp_beta(log2_advantage) * math.sqrt(ct.var)
parameters = gen_params(mult_many_naif(ct, L, r, params), "min_modulus", min_secu_level, True, reduction_cost_model, prv_key_distr)
print "n =",parameters[0], ",estimated_secu_level =",parameters[1], ",size(q) =",parameters[2], ",noise_rate =", parameters[3], parameters[5]

