# A Synced Effects Logic of Esterel

## For both Logical Correctness and Temporal Verification


Esterel is an imperative style language that has found success in many safety-critical applications. Its precise semantics makes it natural for programming and reasoning. Existing techniques tackle either one of its main challenges: correctness checking or temporal verification. To resolve the issues simultaneously, we propose a new solution via a Hoare-style forward verifier and a term rewriting system (T.r.s) on Synced Effects. The first contribution is the novel effects logic computes the deterministic program behaviour via construction rules at the source level, defining program evaluation syntactically. As a second contribution, by avoiding the complex translation from temporal properties to Esterel programs, our purely algebraic T.r.s efficiently checks the temporal properties described by the Synced Effects. We prototype this logic on top of the HIP/SLEEK system and show our method’s feasibility using a number of case studies.

## Online demo

The easiest way to try the code is to use the [Web UI](http://loris-5.d2.comp.nus.edu.sg/SyncedEffects/index.html?ex=fig25&type=c&options=sess) written
by [Yahui Song](https://www.comp.nus.edu.sg/~yahuis/).

### To Compile:

```
git clone https://github.com/songyahui/SyncedEffects.git
cd SyncedEffects
chmod 755 clean 
chmod 755 compile 
./compile
```

### Dependencies:

```
opam switch create 4.07.1
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install z3
```

### Examples:

Entailments Checking 

```
./sleek src/effects/test1.txt 
```

Program Verification

```
./hip src/programs/fig5.txt
```

LTL to Effects Translator

```
./ltl src/ltl/Traffic_light.ltl 
```

### To Clean:

``` 
./clean
```

 
