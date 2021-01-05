attach("isogeny-parameters.sage")

# Simple test function to demonstrate isogeny case for SRA
def testIsoSRA(bits=10, d=50):
    N, P, Eaux, isogenyList = SRAparam(bits)
    M = convertIsogenyList(isogenyList)
    f = generateTestPoly(P,1,d)

    roots_SRA = isoSRA(f, M, Eaux)
    roots = extractRoots(f)
    roots_SRA.sort()
    roots.sort()

    if roots_SRA == roots:
        print "Isogeny maps SRA Test passed."
        return True
    else:
        print "Isogeny maps SRA Test failed"
        return False


# Simple test function to demonstrate p-1 smooth case for SRA
def testSmoothSRA(bits=10,smoothness_bound=3, d = 50):

    P = findNextSmoothPrime(2^bits,smoothness_bound)
    
    f = generateTestPoly(P,1,d)
    M = createSmoothMaps(P)
    roots_SRA = SRA(f,M,[0,1],checkZero=False)
    roots = extractRoots(f)
    roots_SRA.sort()
    roots.sort()

    if roots_SRA == roots:
        print "p-1 smooth maps SRA Test passed."
        return True
    else:
        print "p-1 smooth maps SRA Test failed"
        return False

# Generates a test polynomial
def generateTestPoly(p,n,degree, squareFree=True):
    """
    Generates a split polynomial in the field GF(p^n)[X] for testing the SRA algorithm.
    Input:      p - prime
                n - integer > 1
           degree - degree of polynomial requested
    
    Output: A polynomial in the field GF(p^n)[X] with d roots in GF(p^n)
    """
    F = GF(p**n, "alpha")
    FX = F["X"]
    X = FX.gen()

    if squareFree == False:
        factors = [X - F.random_element() for _ in xrange(degree)]
        return prod(factors)
    elif squareFree == True:
        if degree > p**n:
            print "Creating a squarefree polynomial impossible as degree > p^n. Returning polynomial x^{p^n} - x"
            return X^(p^n) - X
        else:
            factors = {F.random_element() for _ in xrange(degree)}
            while len(factors) < degree:
                factors = factors.union({F.random_element()})
            return prod([X - a for a in factors])
    else:
        print "squareFree must be True or False."
        raise ValueError
    

# Basic function to take list of composable isogenies and create a series of maps acceptable by the SRA algorithm
def convertIsogenyList(listOfIsogenies):
    L = listOfIsogenies
    L = [l.rational_maps()[0] for l in L]
    return [tuple([l.numerator().univariate_polynomial(),l.denominator().univariate_polynomial()]) for l in L]

# A simple function to create smooth maps for a given prime.
# Note that the image of this map is [0,-1] which will be required to extract all values in FP
def createSmoothMaps(p):
    F.<X> = PolynomialRing(GF(p))
    factors = factor(p-1)
    factorList = []
    for i in factors:
        for j in xrange(i[1]):
            factorList.append(i[0])
            
    mapList = [[X^i,F(1)] for i in factorList]
    #mapList[-1][0] += -1
    return [tuple(m) for m in mapList]


# Generic SRA
# Input: f    - a polynomial in K[X] of degree d
#        MAPS - a set of t rational maps in a list of tuples forming the numerator and denominators
# imageValues - the set of point in the image of the composed map K
# Output: roots of f which intersect with the preimage of imageValues

def SRA(poly, maps, imageOfK=[],checkZero=True):
    # Extract basic data from the polynomial
    F = poly.base_ring()
    pn = F.characteristic()**F.degree()
    F.<X,Y> = PolynomialRing(F)
    
    try:
        poly = poly.univariate_polynomial()
    except Exception:
        pass

    if checkZero and poly[0] == 0:
        extra_roots = [F.base_ring()(0)]
    else:
        extra_roots = []

    poly = F(poly(X))
    # Extract basic data from maps
    t = len(maps)
    a = map(lambda m : F(m[0](X)), maps)
    b = map(lambda m : F(m[1](X)), maps)

    # Resultant stage: create list of f^(i) polynomials
    fList = [F(poly)]
    for i in xrange(t-1):
        f_i = fList[-1].resultant(a[i] - b[i]*Y, X)
        f_i = f_i(Y=X)
        f_i = gcd(f_i, X^pn - X)
        fList.append(f_i)
    # Convert back to univariate polynomials for efficiency
    
    # GCD stage:
    candidateRoots = []
    candidateRoots += flatten([extractRoots(gcd(fList[t-1],a[t-1] - b[t-1]*root)) for root in imageOfK])
    candidateRoots += extractRoots(gcd(fList[t-1],b[t-1]))

    for i in xrange(t-2,-1,-1):
        candidateRoots = flatten([extractRoots(gcd(fList[i],a[i] - b[i]*root)) for root in candidateRoots])
        if fList[i+1].degree() < fList[i].degree():
            candidateRoots += extractRoots(gcd(fList[i], b[i]))

    return candidateRoots + extra_roots


def isoSRA(poly, maps, Eaux):
    # Convert polynomial to a polynomial in U
    h = poly.change_variable_name('U')
    FPN_U = h.parent()
    U = FPN_U.gen()
    FPN = poly.base_ring()
    p = FPN.characteristic()

    # Extract elliptic auxillary curve and the Icart conversion map
    L0_numerator, L0denominator = cleanIcartMap(Eaux)

    # Compute the resultant to convert roots in Fp* to points on the auxillary curve
    U,X = L0_numerator.parent().gens()
    f1 = L0_numerator.parent(h).resultant(L0_numerator,U)
    f1 = f1.univariate_polynomial()

    # Note that the degree of the map is 3, so the resultant will be a polynomial of deg(f)*3, but we can reduce by a gcd computation as we are only interested in roots in Fp.
    f1 = gcd(X**p - X, f1)

    
    # Here we call SRA as a subroutine with no point in the image - we are only interested in extracting points "at infinity"

    roots = SRA(f1.univariate_polynomial(),maps,[])
    # We convert the roots back using the Icart formula
    solutionRoots = convertIcartRoots(poly,roots,Eaux)

    # If 0 was a root we add it back in, as the Icart map was only a map to Fp*
    if poly[0].is_zero():
        extra_roots = [0]
    else:
        extra_roots = []

    return solutionRoots + extra_roots
    

def cleanIcartMap(Eaux):
    Fpn = Eaux.base_ring()
    Fpn_xu.<U,X> = PolynomialRing(Fpn)

    a = Eaux.a4()
    b = Eaux.a6()

    v = (Fpn(3)*a - U**4)/(Fpn(6)*U)
    L0 = X**3 + a*X + b - (U*X +v)**2

    return Fpn(1/36)*L0.numerator(), Fpn(1/36)*L0.denominator()

def convertIcartRoots(poly,roots,Eaux):
    if roots == []:
        return []
    else:
        pass
    try:
        poly = poly.univariate_polynomial()
    except Exception:
        pass
    a = Eaux.a4()
    b = Eaux.a6()
    Fpn = Eaux.base_ring()
    Fpn.<u> = PolynomialRing(Fpn)
    poly = poly(u)

    Fpn_roots = []
    for root in roots:
        X = root**3 + a*root + b
        Y = X.square_root()
        if Y in Fpn:
            Fpn_roots.append((root,Y))
            Fpn_roots.append((root,-Y))
        else:
            pass
    ans = []

    for root in Fpn_roots:
        x, y = root
        temp = u**4 - Fpn(6)*x*u**2 + 6*u*y - 3*a
        temp = gcd(temp, poly)
        ans += temp.roots(multiplicities=False)
    return ans


# Convert elliptic curve in sage into a two variable polynomial x^3 + a*x + b
def getPolynomial(curve):
    F.<X,Y> = PolynomialRing(curve.base_ring())
    curve = curve.defining_polynomial()(z=1,y=0).univariate_polynomial()
    return curve

def createIsogenyMaps(numBits):
    N, p, Eaux, isogenyList = SRAparam(numBits)

    F.<x> = PolynomialRing(GF(p))
    
    M0_numerator = getPolynomial(Eaux)(Y=0)(X=x)
    M0_denominator = F(1)
    M1_numerator = x**2
    M1_denominator = F(1)

    
    MAPS = [tuple([M0_numerator,M0_denominator]), tuple([M1_numerator,M1_denominator])] + convertIsogenyList(isogenyList)

    return p,MAPS

def convertSquare(pts):
    temp = []
    for pt in pts:
        temp.append(pt.square_root(all=True,extend=False))

    return flatten(temp)


def convert(pts,Eaux):
    EauxPoly = getPolynomial(Eaux)

    pts = map(lambda x: EauxPoly(x), pts)

    pts = convertSquare(pts)

    return pts




def findNextSmoothPrime(N,B):
    N = next_prime(N-1)
    ans = smartFactor(N - 1,B)
    while ans == False:
        N = next_prime(N)
        ans = smartFactor(N -1,B)
    return N

# Returns the B-smooth factorization of n if possible, False if not. O(log n)
# Defaults to assuming efficient smooth factorization without known B-smooth bound.
def smartFactor(n,B=None, unique=False):
    if B == None:
        return extractFactors(n,unique)
    else:
        pass
    B = prime_range(B+1)
    factors = []
    for b in B:
        while n % b == 0:
            factors.append(b)
            n = n // b
        if n == 1:
            if unique == True:
                return unique_list(factors)
            else:
                return factors
    return False
