from scipy.stats import norm
from random import randint
import numpy as np
import random 
import math
from scipy.special import erfc, erfcinv, erf, erfinv
import matplotlib as plt
from functools import reduce
#load('https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py')

#Initial parameters
params = {'n':2048,'sigma':3.2,'_lambda': 128,'t':2,'q':None, 
            'h':63, 'ell': None, 'T': 2**32, 'delta_r': None}
params['q'] = 2**100 # q = size(n) ciphertext modulus
params['ell'] = math.ceil(math.log(params['q'],params['T'])) # 
params['delta_r'] = math.sqrt(params['n']) #expansion factor
Delta = math.floor(params['q']/params['t']) # q/t

# X <- N(0, sig)
# ||X|| < beta * sig w/ proba = 1 - epsilon
def comp_beta(log2_epsilon):
    return math.ceil(math.sqrt(2)*erfcinv(2**(-log2_epsilon)))

#failure probability
def failure_proba(x, sigma, k): #P(|x| > k*sigma)
    return erfc(k/math.sqrt(2))

#variance of fresh ciphertexts
def variance():
    return (1 + 2*params['n']/3 + params['h']) * (NoiseGaussianWidth(params['n'], 
                                                        security_reduction=False)**2)
# log(x)/log(2)
def log2(x):
    return math.ceil(math.log(x)/math.log(2)) 

# compute Delta/2
def max_dec_noise(params):
    return (math.floor(params['q']/params['t'])*(1+params['t']) - params['q'])/2 
"""
- Bound on error distribution: B_err = 10*sigma , to be statistically
indistinguishable, with a probability 2^(-64) from a discrete Gaussian distribution
with noise Gaussian width sigma.

- 
"""

#Polynomial class 
class poly(object):
    def __init__(self, d, norm):
        self.norm = norm #infinite norm
        self.d = d # non zero coeffs 
    
    def powers_of(self, T):
        #for i in range(math.log(params['q'],[T])):
            #self.p[i] = poly_mod(self.p * T**i, params['q'])
        res = poly(d=0,norm=0)
        res.norm = self.norm * T**(ell-1) % (params['q']/2)
        res.d = self.d
        
        return res
    
    def decomp(self, T):
        #for i in range(math.log(params['q'],[T])):
            #self.p[i] = poly_mod(self.p[i], T)
        res = poly(d=0,norm=0)
        res.norm = T >> 1
        res.d = self.d
        
        return res

    #|p|_2 <= sqrt(p.d) * |p|_infty (https://en.wikipedia.org/wiki/Norm_(mathematics))
    def norm2(p):
        return math.sqrt(p.d) * p.norm

    def add(self, other):

        return poly(max(self.d, other.d), self.norm + other.norm)

    def mult(self, other):

        res = poly(d = self.d + other.d, norm = params['delta_r'] * self.norm * other.norm)
        if res.d > params['n']:
            res.d = params['n']

        return res

#Relinearization key class
class rlk(object):
    def __init__(self, d, var, T, msg):
        self.d = d #non zero coeffs
        self.var = var #variance
        self.T = params['T'] #decomp basis
        self.msg = poly(0,0)
        #self.i = i # i-th relin key 

#Ciphertext class
class ctxt(object):

    def __init__(self, d, var, msg):
        self.var = var #variance(self) 
        self.d = d   
        self.msg = msg

    #addition of two ciphertexts: Outputs a ciphertext
    def add(self, other, rlk, r):

        return ctxt(d = max(self.d, other.d), 
                            var = self.var + other.var, 
                            msg =  poly.add(self.msg, other.msg))
    
    #multiply ctxt w/ plain polynomial: Outputs a ciphertext
    def mult_plain(self, p):
        res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))

        res.d = self.d
        res.var = p.d * p.norm * self.var
        res.msg = poly.mult(self.msg, p)    
        return res

    #multiply two ciphertexts: Outputs a ciphertext
    def mult(self, other, rlk, r): 
        # r = t*r_i = poly(n, t*sqrt(n)/2 + 2*t -1/2)
        # we do not use mult_plain to compute Var(r*v)
        # use Var(r * v) = (sqrt(n)*sig(r))**2 * Var(v) instead 
        
        res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))

        if (self.d == 0) or (other.d == 0):
            return res

        p1 = ctxt.mult_plain(self, other.msg) # m1 * v2
        p2 = ctxt.mult_plain(other, self.msg) # m2 * v1

        r1 = ctxt.mult_plain(self, r) # r * v1
        r2 = ctxt.mult_plain(other, r) # r * v2

        
        res1 = ctxt.add(p1, p2, rlk, r)
        res2 = ctxt.add(r1, r2, rlk, r)
        res = ctxt.add(res1, res2, rlk, r)
        res.d = self.d + other.d - 1 
        return ctxt.relin(res, rlk)#relinearisation of the result

    #relinearization 
    def relin(self, rlk):
        e = ctxt.keyswitch(self, rlk)
                
        return ctxt.add(self, e, rlk, poly(0,0))
    
    #keyswitch key 
    def keyswitch(self, rlk):
        #transform c2 to poly of norm T/2
        p = poly(d=0, norm=0)
        c2 = poly.decomp(p, rlk.T)
        res = ctxt(d=0, var=0, msg = poly(0,0))
        for i in range(params['ell']):
            res = ctxt.add(res, ctxt.mult_plain(rlk, c2), rlk, p)
        return res

    #ct_f=FV.Mult(ct_1,FV.Mult(ct_2,FV.Mult(...,FV.Mult(ct_k,ct_k+1))))
    def mult_many_naif(self, rlk, r, params):

        res = self[0]

        for i in range(1,len(self)):
            res = ctxt.mult(res, self[i], rlk, r)

        if ctxt.is_valide(res, params):
            return res
    
        print("Circuit not handeled, decryption failure")
        print("Generating new parameters...")
        nq = MinCorrectModulus(res)
        print(log2(nq))
        return res

    def mult_many(self, rlk, r, params):

        res = ctxt(d=0, var=0, msg = poly(0,0))
        k = len(self)
        N = [None]*k

        for i in range(k):
            N[i] = (self[i].msg).d * (self[i].msg).norm # N_i = ||m_i||_2
        alpha = r.norm # exception alpha = Var(r)

        tmp1 = 1
        for i in range(2,k):
            tmp1 *= (N[i] + alpha)
        var0 = (N[1] + alpha) * tmp1 * self[0].var
        var1 = (N[0] + alpha) * tmp1 * self[1].var

        var = [0]*(k-1); tmp3 = 1; tmp4 = 1

        for j in range(2, k-1):
            for i in range(j+1, k):
                tmp3 *= (N[i] + alpha)

            for l in range(0, j):
                tmp4 *= N[l]

            var[j] = tmp3 * (tmp4 + alpha) * self[j].var
            tmp3 = 1; tmp4 = 1

        tmp5 = 1
        if k > 2:
            for i in range(k-1):# ok
                tmp5 *= N[i]
            vark = (tmp5 + alpha)*self[k-1].var
        else: vark = 0

        res.var = var0 + var1 + sum(var[j] for j in range(k-1)) + vark

        for i in range(0,k):
            res.msg = poly.mult(res.msg, self[i].msg)
        
        return ctxt.relin(res, rlk)

    def exponontiate(self, rlk, r):
        return ctxt.mult(self, self, rlk, r)

    def comb(self, rlk, r, k,params):
        res = self[0]
        circ = gen_random_circuit(k-1)
        print(circ)
        tmp = []
    
        for i in range(1,len(self)):
            res = circ[i-1](res, self[i], rlk, r)

        if ctxt.is_valide(res, params):
            return res
        
        print("Circuit not handeled, decryption failure")
        print("Generating new parameters...")
        nq = MinCorrectModulus(res)
        print(log2(nq))
                
        return res

    #condition for correctness 
    def is_valide(self, params):
        if comp_beta(log2_epsilon) * math.sqrt(self.var) < max_dec_noise(params):
            return True
        else: return False

#generate random circuit of length k
def gen_random_circuit(k): 
    operations = [ctxt.add, ctxt.mult] 
    circuit = [None]*k
    #random.seed(42)
    for i in range(k):
        circuit[i] = random.choice(operations)
    
    #print(circuit)
    return circuit

#ciphertexts are given as inputs of the circuit
def gen_inputs(k):

    inputs = [ctxt(0,0,poly(0,0))]*k
    msg = poly(d = params['n']//2, norm = params['t'] -1)

    for i in range(k):
        inputs[i] = ctxt(2, variance(), msg)

    return inputs
    
#Generate a set of params then check correctness and security level using albrecht's primal_usvp(LWE-Estimator)
def MinCorrectModulus(circuit):
    q = params['q']
    new_params = {'n':params['n'], 'q': q, 't':params['t']}
    while ctxt.is_valide(circuit, new_params) == False:
        q <<= 2
        new_params['q'] = q
    q >>= 2

    return q

def NoiseGaussianWidth(n,security_reduction):
    if security_reduction:
        return 2*math.sqrt(n)        #Regev     
    else:
        return 8/math.sqrt(2*math.pi)     #Peikert
                     

#main
log2_epsilon = 64 
rlkey = rlk(2, 3.2, params['T'], None)
r_var = params['n'] * params['h'] * params['t'] / 12 #params['t']*params['delta_r']//2 + 2*params['t'] 
res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))
r = poly(d = 1, norm = r_var) 
msg = poly(d = params['n']/2, norm = params['t'] -1)
#msg2 = poly(d = params['n']//2, norm = params['t'] -1)
ct1 = ctxt(2, variance(), poly(d = params['n']//2, norm = params['t'] -1))

k=3
inputs = gen_inputs(k)
ct = [ct1]*k
print("Circuit w/ mults and adds")
print(ctxt.comb(inputs, rlkey, r, k, params).var)
print("Circuit w/ mults only")
print(ctxt.mult_many_naif(ct, rlkey, r, params).var)
print(ctxt.mult_many(ct, rlkey, r, params).var)

