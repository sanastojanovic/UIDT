(*

                          ===== Mastermind - best starting move =====

Mastermind is a code-breaking game for two players.
One player (the codemaker) creates a code by choosing a secret sequence of four letters
from a set of available letters called the alphabet (A, B, C, D, E, F).
The other player (the codebreaker) tries to guess the sequence in as few attempts as possible.

After each guess, the codemaker provides feedback:
Bulls: number of correct letters that are in the correct position.
Cows: number of correct letters that are in the wrong position.

The codebreaker uses this feedback to refine subsequent guesses,
with the goal of determining the exact secret sequence.



                                ===== Knuths Algorithm =====

There are 6^4=1296 different possible codes.
Donald Knuth published a five-guess algorithm in 1976–77 (“The Computer as Master Mind”),
which recommended starting with AABB, and guaranteed solving any puzzle in 5 turns,
while solving it on average in 4.48 turns.

However, Knuth didn't formally prove that AABB is the best first guess.
He simply used a minimax algorithm, ran it through all possible combinations,
and found that AABB gave the best results on average.

With most people who play Mastermind being primarily kids,
and often unfamiliar with Knuth’s findings,
starting moves vary - with the two most common being AABB and AAAB.



                             ===== What IS the "best" move =====


Here we will, formally prove the BEST starting move.

To accomplish this we need to compare every possible code and find the best one.

First we need to define what "best" means.

Let S be the set of all possible solutions to the puzzle (|S₀| = 1296).
After a guess g, the codebreaker receives feedback r = (bulls, cows):
1) r = (4,0) \<rightarrow> guess is correct and codebreaker solved the puzzle
2) otherwise \<rightarrow> guess is not correct and we find every code in S that would give same feedback 
when compared to g (one of those codes is solution to the puzzle).
We place all found codes in new set S_after.  

Therefore, we will define a guess g_1 being better then guess g_2, if, on average, 
size of S_after is smaller after g_1, then g_2.
We assign value called average_remaining to each code g_i.

Code g_b is the "best" starting code if:
average_remaining(g_b) \<ge> average_remaining(g_i), \<forall>i \<in> {1,2..n}, i \<noteq> k, n-number of possible guesses

                    

                   ===== Reducing the number of possible candidates =====

In order to find the best code we do not need to compare all 1296 possible codes. 
We can drastically reduce set of possible best codes by recognizing that:
1) average_remaining(g) = average_remaining(g'), where g' is permutation of g
(average_remaining AABB = average_remaining ABBA = average_remaining BBAA = average_remaining BAAB).

2) average_remaining(g) = average_remaining(g'), where g' is obtained from g by replacing all 
occurrences of one letter from g with another (not necessarily different) letter from the alphabet.
(average_remaining ABCD = average_remaining ABCE = average_remaining ABCF = ...)

*I DID NOT PROVE THESE ASSUMPTIONS*

Finally we can reduce all possible combinations to these candidates:
AAAA, AAAB, AABB, AABC, ABCD

*)

theory Mastermind
  imports Main "HOL.Real" "HOL-Library.Multiset"
begin

datatype alphabet = A | B | C | D | E | F
type_synonym code = "alphabet list"

(*--Generates all possible codes with length n, using letters from xs--*)
fun replicateM :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "replicateM 0 xs = [[]]" |
  "replicateM (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>x. x # ys) xs) (replicateM n xs))"

(*--Generates all possible codes with length 4 from alphabet (A,B,C,D,E,F)--*)
definition all_codes_list_ABCDEF :: "code list" where
  "all_codes_list_ABCDEF = replicateM 4 [A, B, C, D, E, F]"


                              (*==== Bulls and Cows ====*)

(*--returns number of times letter X appeared in a code--*)
fun count_letters :: "alphabet \<Rightarrow> code \<Rightarrow> nat" where
  "count_letters c [] = 0" |
  "count_letters c (x#xs) = (if x = c then 1 else 0) + count_letters c xs"

lemma count_letters_le_length:
  "count_letters c xs \<le> length xs"
  by (induction xs) auto


(*--returns number of correct letters in the correct places--*)
fun bulls :: "code \<Rightarrow> code \<Rightarrow> nat" where
  "bulls [] [] = 0" |
  "bulls (x#xs) (y#ys) = (if x = y then 1 else 0) + bulls xs ys" |
  "bulls _ _ = 0"

lemma bulls_le_length:
  "length g = length s \<Longrightarrow> bulls g s \<le> length g"
  by (induction g s rule: bulls.induct) auto

(*--returns number of correct letters in the incorrect places--*)
definition cows :: "code \<Rightarrow> code \<Rightarrow> nat" where
  "cows g s = (
     let letters = [A,B,C,D,E,F];
         shared = sum_list (map (\<lambda>c. min (count_letters c g) (count_letters c s)) letters)
     in shared - bulls g s
   )"

(*--returns a pair r = (bulls, cows)--*)
definition feedback :: "code \<Rightarrow> code \<Rightarrow> (nat\<times>nat)" where
  "feedback g s = (bulls g s, cows g s)"


                                 (*==== S after subset ====*)

(*--returns S after--*)
fun S_after :: "code \<Rightarrow> code list \<Rightarrow> (nat\<times>nat) \<Rightarrow> code list" where
  "S_after g codes r = filter (\<lambda>s. feedback g s = r) codes"

lemma S_after_subset:
  "set (S_after g codes r) \<subseteq> set codes"
  by simp

lemma S_after_correct:
  "\<forall>s \<in> set (S_after g codes r). feedback g s = r"
  by simp

lemma S_after_filter_stable:
  "S_after g (S_after g codes r) r = S_after g codes r"
  by simp

lemma S_after_valid_feedback:
  assumes "s \<in> set (S_after g codes r)"
  shows "feedback g s = r"
  using assms by simp

(*--returns list of values, where each value is size of S_after, for each possible feedback r--*)
definition remaining_sizes :: "code \<Rightarrow> code list \<Rightarrow> nat list" where
  "remaining_sizes g codes = map (\<lambda>r. length (S_after g codes r)) (map (feedback g) codes)"

lemma length_remaining_sizes:
  "length (remaining_sizes g codes) = length codes"
  by (simp add: remaining_sizes_def)

lemma remaining_sizes_nonneg:
  "\<forall>n \<in> set (remaining_sizes g codes). n \<ge> 0"
  by (simp add: remaining_sizes_def)

(*--returns average remaining size of all possible S_after subsets--*)
definition average_remaining :: "code \<Rightarrow> code list \<Rightarrow> real" where
  "average_remaining g codes =
     (let sizes = remaining_sizes g codes
      in (sum_list (map real sizes)) / real (length sizes))"


                          (*==== Checking all possible candidates ====*)

(*--list of all candidate best guesses--*)
definition all_guesses :: "code list" where
  "all_guesses = [[A,A,A,A], [A,A,A,B], [A,A,B,B], [A,A,B,C], [A,B,C,D]]"

(*--pair (guess, average_remaining)--*)
definition guess_avg_pairs :: "(code \<times> real) list" where
  "guess_avg_pairs = map (\<lambda>g. (g, average_remaining g all_codes_list_ABCDEF)) all_guesses"

(*--sorts all guesses, using average_remaining value--*)
definition sorted_guesses :: "(code \<times> real) list" where
  "sorted_guesses = sort_key snd guess_avg_pairs"

value "sorted_guesses"
(*
AABC - 185.27
ABCD - 188.19
AABB - 204.53
AAAB - 235.95
AAAA - 511.98
*)

(*
With AABC reducing the set S to an average of 185.27 possible combinations,
we can deduce that it is the best possible starting move according to our definition.

However, this does not mean Knuth was wrong.
Our definition of the best starting move, although reasonable, is not complete.
We would need to take into account the reduction of S based on combinations of guesses,
their order, different feedback outcomes, and possibly other factors I haven’t even considered.

Finally, with all that said, it really does not matter.
Mastermind puzzles cannot be reliably solved in under four moves,
and the puzzle is always solvable in five or fewer moves (if played optimally)
using almost any starting combination (except AAAA).
*)

end
