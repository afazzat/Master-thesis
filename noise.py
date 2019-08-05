from scipy.stats import norm
from random import randint
import numpy as np
import random 
import math
from scipy.special import erf
import matplotlib as plt
from functools import reduce
import urllib.request
LWE_Estimator  = urllib.request.urlopen('https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py')
#Initial parameters
params = {'n':2048,'sigma':3.2,'_lambda': 128,'t':2,'q':None, 
			'H':63, 'ell': None, 'T': 2**32, 'delta_r': None}
params['q'] = 2**87 # q = size(n)
params['ell'] = math.ceil(math.log(params['q'],params['T']))
params['delta_r'] = math.sqrt(params['n']) 
max_dec_noise = (params['q']/(2*params['t']))

"""
- Bound on error distribution: B_err = 10*sigma , to be statistically
indistinguishable, with a probability 2^(-64) from a discrete Gaussian distribution
with noise Gaussian width sigma.

- 
"""

#set coeffs [coeff]_q of a polynomial
def poly_mod(poly, modulo):
	for i in range(len(poly)): #poly given w/ the list of its coeffs
		while 2*poly[i] > modulo: 
			poly[i] -= modulo # -q/2 <= [coeff]_q <= q/2
			
#norm
"""
def norm(x):
	return max([abs(a) for a in x])

#degree of poly
def poly_degree(poly):
	c = 0
	for i in range(len(poly)+1):
		if poly[i]:
			c+=1
	#return np.polynomial.Polynomial.degree(poly) + 1
	return c
"""
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

	def add(self, other):

		return poly(max(self.d, other.d), self.norm + other.norm)

	def mult(self, other):

		res = poly(d = self.d + other.d, norm = params['delta_r'] * self.norm * other.norm)
		if res.d > params['n']:
			res.d = params['n']

		return res

class rlk(object):
	def __init__(self, d, var, T, msg):
		self.d = d #non zero coeffs
		self.var = var #variance
		self.T = params['T'] #decomp basis
		self.msg = poly(0,0)
		#self.i = i # i-th relin key 

class ctxt(object):

	def variance():

		return (1 + 2*params['n']/3 + params['H']) * (params['sigma']**2)

	def __init__(self, d, var, msg):
		self.var = var #variance(self) 
		self.d = d   
		self.msg = poly(0,0)


	def add(self, other): # ctxt + ctxt = ctxt

		return ctxt(d = max(self.d, other.d), 
							var = self.var + other.var, 
							msg =  poly.add(self.msg, other.msg))
	
	def mult_plain(self, p):
		"""multiply ctxt w/ poly """
		res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))

		res.d = self.d
		res.var = p.d * p.norm * self.var
		res.msg = poly.mult(self.msg, p)
		return res

	
	def mult(self, other, rlk, r): # r = t*r_i = poly(n, t*sqrt(n)/2 + 2*t -1/2)
		""" multiply ctxt w/ ctxt"""
		res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))
		p1 = poly.add(self.msg, r)
		p2 = poly.add(other.msg, r)

		if (self.d == 0) or (other.d == 0):
			return res

		else:
			res =  ctxt.add(ctxt.mult_plain(self, p2),ctxt.mult_plain(other, p1))
			res.d = self.d + other.d - 1 
			return ctxt.relin(res, rlk)#relinearisation of the result

	def relin(self, rlk):
		e = ctxt.keyswitch(self, rlk)
				
		return ctxt.add(self, e)
	
	def keyswitch(self, rlk):
		#transform c2 to poly of norm T/2
		p = poly(d=0, norm=0)
		c2 = poly.decomp(p, rlk.T)
		res = ctxt(d=0, var=0, msg = poly(0,0))
		for i in range(params['ell']):
			res = ctxt.add(res, ctxt.mult_plain(rlk, c2))
		return res

	#ct_f=FV.Mult(ct_1,FV.Mult(ct_2,FV.Mult(...,FV.Mult(ct_k,ct_k+1))))
	def mult_many(self, rlk, r):

		res = self[0]

		for i in range(1,(len(self))):
			res = ctxt.mult(res, self[i], rlk, r)

		if ctxt.is_valide(res) :
			return res
		else: 
			print("Circuite not handeled, decryption failure")

		return res

	def is_valide(self):
		if 6 * math.sqrt(self.var) < max_dec_noise:
			return True
		else: return False

#Generate a set of params then check correctness and security level using albrecht's primal_usvp(LWE-Estimator)
class parameter_selection(object):
	"""docstring for parameter_selection"""
	def __init__(self, arg):
		super(parameter_selection, self).__init__()
		self.arg = arg

	
	def MinSecureDegree(q, _lambda, sigma):
		n = params['n']
		first_pass = True

		while first_pass or not secure :
			first_pass = False
			noise_rate = params['sigma']/params['q']
			_lambda = LWE-Estimator()
			n = n*2
		n = n/2

		return (n, params['sigma']/params['q'], _lambda)

	def MinCorrectModulus(n, sigma, circuite, t, T):
		q = params['q']
		first_pass = True
		while first_pass or not ctxt.is_valide(circuite):
			first_pass = False

	def ChooseParam():
		0


rlkey = rlk(2, 3.2, params['T'], None)
rnorm = params['t']*params['delta_r']//2 + 2*params['t'] 
res = ctxt(d = 0, var = 0, msg = poly(d = 0, norm = 0))
r = poly(d = params['n'], norm = rnorm)
msg = poly(d = params['n']//2, norm = params['t'] -1)
#msg2 = poly(d = params['n']//2, norm = params['t'] -1)
ct1 = ctxt(2, ctxt.variance(), msg)
ct2 = ctxt(2, ctxt.variance(), msg)
ct3 = ctxt(2, ctxt.variance(), msg)
ct = [ct1, ct2, ct3, ct1, ct2, ct3, ct2, ct3, ct1, ct3]
print(ctxt.mult_many(ct, rlkey, r).var)

#print(LWE_Estimator.read())