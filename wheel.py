from sys  import argv
from math import log
from time import time

# non standard packages
from bitarray import bitarray

# tuning parameters
CUTOFF      = 1e4           # small for debug       
SIEVE_SIZE  = 2 ** 20       # in bytes, tiny (i.e. 1) for debug
CLOCK_SPEED = 1.6           # in GHz, on my i5-6285U laptop


def progress(current, total):
    """Display a progress bar on the terminal."""
    size = 60
    x = size * current // total
    print(f'\rSieving: [{"#" * x}{"." * (size - x)}] {current}/{total}', end="")


def seg_wheel_stats(n):
    """Returns only the stats from the segmented sieve."""
    return(segmentedSieve(n, statsOnly=True))


def print_sieve_size(sieve):
    print("sieve size:", end=' ')
    ss = len(memoryview(sieve))
    print(ss//1024, "KB") if ss > 1024 else print(ss, "bytes")


def prime_gen_wrapper(n):
    """
    Decide whether to use the segmented sieve or a simpler version.  
    Stops recursion.
    """
    return smallSieve(n + 1) if n < CUTOFF else segmentedSieve(n)
    # NB: rwh_primes1 (a.k.a. smallSieve) returns primes < N.
    # We need sieving primes <= sqrt(limit), hence the +1


def smallSieve(n):
    """Returns a list of primes less than n."""
    # a copy of Robert William Hanks' odds only rwh_primes1
    #     used to get sieving primes for smaller ranges
    #     from https://stackoverflow.com/a/2068548/11943198
    sieve = [True] * (n // 2)
    for i in range(3, int(n ** 0.5) + 1, 2):
        if sieve[i // 2]:
            sieve[i * i // 2::i] = [False] * ((n - i * i - 1) // (2 * i) + 1)
    return [2] + [2 * i + 1 for i in range(1, n // 2) if sieve[i]]


class PrimeMultiple:
    """Contains information about sieving primes and their multiples"""
    __slots__ = ['prime', 'multiple', 'wheel_index']

    def __init__(self, prime):
        self.prime = prime

    def update(self, multiple, wheel_index):
        self.multiple = multiple
        self.wheel_index = wheel_index

    def update_new_mult(self, multiple, wheel_index, wheel):
        self.update(multiple, wheel_index)
        wheel.inc_mults_in_use() 


class m30_wheel:
    """Contains all methods and data unique to a mod 30 (2, 3, 5) wheel"""
    # mod 30 wheel factorization based on a non-segmented version found here
    #     https://programmingpraxis.com/2012/01/06/pritchards-wheel-sieve/
    #  in a comment by Willy Good

    def __init__(self, sqrt):
        # mod 30 wheel constant arrays
        self.skipped_primes   = [2, 3, 5]      # the wheel skips multiples of these
        self.wheel_primes     = [7, 11, 13, 17, 19, 23, 29, 31]
        self.wheel_primes_m30 = [7, 11, 13, 17, 19, 23, 29, 1]

        self.gaps             = [4,2,4,2,4,6,2,6, 4,2,4,2,4,6,2,6]  # 2 loops for overflow

        self.wheel_indices    = [0,0,0,0,1,1,2,2,2,2, 3,3,4,4,4,4,5,5,5,5, 5,5,6,6,7,7,7,7,7,7]
        self.round2wheel      = [7,7,0,0,0,0,0,0,1,1, 1,1,2,2,3,3,3,3,4,4, 5,5,5,5,6,6,6,6,6,6]


        # get sieving primes recursively,
        #   skipping over those eliminated by the wheel
        self.mults = [PrimeMultiple(p) for p in prime_gen_wrapper(sqrt)[len(self.skipped_primes):]]
        self.mults_in_use = 0

    def inc_mults_in_use(self):
        self.mults_in_use += 1

    def get_skipped_primes(self):
        """Returns tiny primes which this wheel ignores otherwise"""
        return self.skipped_primes

    def num2ix(self, n):
        """Return the wheel index for n."""
        n = n - 7  # adjust for wheel starting at 7 vs. 0
        return (n//30 << 3) + self.wheel_indices[n % 30]

    def ix2num(self, i):
        """Return the number corresponding wheel index i."""
        return 30 * (i >> 3) + self.wheel_primes[i & 7]

    def cull_one_multiple(self, sieve, lo_ix, high, pm):
        """Cull one prime multiple from this segment"""
        p = pm.prime 
        wx = pm.wheel_index 
        mult = pm.multiple - 7     # compensate for wheel starting at 7 vs. 0
        p8 = p << 3
        for j in range(8):
            cull_start = ((mult // 30 << 3) 
                         + self.wheel_indices[mult % 30] - lo_ix)
            sieve[cull_start::p8] = False
            mult += p * self.gaps[wx]
            wx += 1

        # calculate the next multiple of p and its wheel index

        # f = next factor of a multiple of p past this segment
        f = (high + p - 1)//p
        f_m30 = f % 30
        # round up to next wheel index to eliminate multiples of 2,3,5
        wx = self.round2wheel[f_m30]
        # normal multiple of p past this segment
        mult = p * (f - f_m30 + self.wheel_primes_m30[wx])
        pm.update(mult, wx)         # save multiple and wheel index

    def cull_segment(self, sieve, lo_ix, high):
        """Cull all prime multiples from this segment"""
        # generate new multiples of sieving primes and wheel indices
        #   needed in this segment
        for pm in self.mults[self.mults_in_use:]:
            p = pm.prime
            psq = p * p
            if psq > high:
                break
            pm.update_new_mult(psq, self.num2ix(p) & 7, self)

        # sieve the current segment
        for pm in self.mults[:self.mults_in_use]: 
            # iterate over all prime multiples relevant to this segment
            if pm.multiple <= high:
                self.cull_one_multiple(sieve, lo_ix, high, pm)

def segmentedSieve(limit, statsOnly=False):
    """
    Sieves potential prime numbers up to and including limit.

    statsOnly (default False) controls the return.
        when False, returns a list of primes found.
        when True,  returns a count of the primes found.
    """
    # segmentation originally based on Kim Walisch's
    #   simple C++ example of segmantation found here:
    #   https://github.com/kimwalisch/primesieve/wiki/Segmented-sieve-of-Eratosthenes

    assert(limit > 6)
    sqrt = int(limit ** 0.5)
    wheel = m30_wheel(sqrt)
    lim_ix = wheel.num2ix(limit)
    sieve_bits = SIEVE_SIZE * 8
    while (sieve_bits >> 1) >= max(lim_ix, 1):
        sieve_bits >>= 1          # adjust the sieve size downward for small N

    sieve = bitarray(sieve_bits)
    num_segments = (lim_ix + sieve_bits - 1) // sieve_bits  # round up
    show_progress = False
    if statsOnly:   # outer loop?
        print_sieve_size(sieve)
        if limit > 1e8:
            show_progress = True

    outPrimes = wheel.get_skipped_primes()  # these may be needed for output
    count = len(outPrimes)

    # loop over all the segments
    for lo_ix in range(0, lim_ix + 1, sieve_bits):
        high = wheel.ix2num(lo_ix + sieve_bits) - 1
        sieve.setall(True)
        if show_progress:
            progress(lo_ix // sieve_bits, num_segments)

        wheel.cull_segment(sieve, lo_ix, high)

        # handle any extras in the last segment
        top = lim_ix - lo_ix + 1 if high > limit else sieve_bits

        # collect results from this segment
        if statsOnly:
            count += sieve[:top].count()  # a lightweight way to get a result
        else:
            for i in range(top):  # XXX not so lightweight
                if sieve[i]:
                    x = i + lo_ix
                    # ix2num(x) inlined below, performance is sensitive here
                    p = 30 * (x >> 3) + wheel.wheel_primes[x & 7]
                    outPrimes.append(p)

    if show_progress:
        progress(num_segments, num_segments)
        print()

    return count if statsOnly else outPrimes

if __name__ == '__main__':
    a=10**10

    n = int(float(a))

    start = time()
    count = segmentedSieve(n, statsOnly=True)
    elapsed = time() - start

    BigOculls = n * log(log(n, 2), 2)
    cycles = CLOCK_SPEED * 1e9 * elapsed
    cyclesPerCull = cycles/BigOculls

    print(f"pi({a}) = {count}")
    print(f"{elapsed:.3} seconds, {cyclesPerCull:.2} cycles/N log log N)")

    print(len(segmentedSieve(n)))
