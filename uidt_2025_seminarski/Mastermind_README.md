# Mastermind – Best Starting Move (Formal Proof in Isabelle/HOL)

This project provides a **formal Isabelle/HOL model** of the classic **Mastermind** code-breaking game,
aiming to determine the *best possible starting move* according to a formal definition of optimality.

## Overview

Mastermind is a two-player game where one player (the codemaker) creates a secret code consisting of four letters chosen from an alphabet `{A, B, C, D, E, F}`.
The other player (the codebreaker) tries to guess the sequence, receiving feedback after each attempt in the form of:

* **Bulls** — correct letters in the correct position
* **Cows** — correct letters in the wrong position

The project defines the full logic of the game in Isabelle, including:

* generation of all possible codes,
* computation of feedback (bulls & cows),
* filtering of possible solutions after each guess, and
* computation of the **average remaining search space** after each guess.

## The Goal

We formally define a metric called `average_remaining`, representing the average number of possible solutions left after a given first guess.
A guess is considered *better* if it minimizes this expected remaining set.

To reduce computation, we consider only representative candidates (under permutation and letter-renaming symmetry):

```
AAAA, AAAB, AABB, AABC, ABCD
```

## Results

After evaluation in Isabelle, the results are:

AABC  - 185.27

ABCD  - 188.19

AABB  - 204.53            

AAAB  - 235.95

AAAA  - 511.98

According to this definition, **AABC** produces the smallest average remaining search space
and is therefore the *best starting move* by our formal metric.

## How to Run

1. Open the project in **Isabelle/HOL**.
2. Load the `Mastermind.thy` theory file.
3. Evaluate the command:

   ```isabelle
   value "sorted_guesses"
   ```
   Isabelle will output the sorted list of candidate guesses by their average remaining value.

## Notes

* Implemented entirely in Isabelle/HOL.
* Based on the 1976 paper *“The Computer as Master Mind”* by Donald Knuth.
* This formalization focuses on *average-case reduction*, not minimax performance.

