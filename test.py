num_points=5000
n = 1024
import numpy as np
import scipy.stats as stats
import matplotlib.pyplot as plt
import pylab
import random
import math
from scipy.special import erfinv

colors=['red', 'blue', 'grey']

def sample(): 
    e = np.poly1d([]) 
    unif_lst = [random.uniform(0,1) for _ in range (n+1)]
    e_list = [(math.sqrt(2.)*(2.1)*erfinv(2*unif_lst[i]-1)) for i in range (n+1)]
    for j in range(n):
        e[j]= random.choice(e_list)
    return e

#list_poly = [np.poly1d([])]*num_points

list_poly = [sample() for _ in range(num_points)] 
    
def add(k):
    s = np.poly1d([])
    for j in range(k):
        s = np.polyadd(s, random.choice(list_poly))
    return s

plt.hist([add(2)[i] for i in range(n)], 50, normed=True, color=colors[0], label='n=1')
plt.hist([add(10)[i] for i in range(n)], 50, normed=True, color=colors[1], label='n=1')
plt.hist([add(50)[i] for i in range(n)], 50, normed=True, color=colors[2], label='n=1')
plt.show()
