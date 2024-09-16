theory "Sorting_Pairwise_Sums"
  imports Main
begin

(* Author: Nemanja Rsumovic 91/2020 *)

definition operation :: "int \<Rightarrow> int \<Rightarrow> int" ("\<oplus>") where
  "\<oplus> x y = x + y"

(* Pairwise sums function: computes all pairwise sums of two lists *)
fun pairwise_sums :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "pairwise_sums [] _ = []" |
  "pairwise_sums (x#xs) ys = (map (\<lambda>y. \<oplus> x y) ys) @ (pairwise_sums xs ys)"

value "pairwise_sums [1,2] [3,4]"            (* Expected result: [4, 5, 5, 6] *)
value "pairwise_sums [1,2,3] [1000,100,10]"  (* Expected result: [1001, 101, 11, 1002, 102, 12, 1003, 103, 13] *)

(* Lemma: Pairwise sums of an empty first list *)
lemma pairwise_sums_empty1[simp]: 
  shows "pairwise_sums [] ys = []"
  by simp

(* Lemma: Pairwise sums of an empty second list *)
lemma pairwise_sums_empty2[simp]:
  shows "pairwise_sums xs [] = []"
  by (induct xs, auto)

value "pairwise_sums [] [3,4]"
value "pairwise_sums [1,2] []"

(* Sorting the pairwise sums *)
definition sortsums :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "sortsums xs ys = sort (pairwise_sums xs ys)"

value "sortsums [1,2] [3,4]"            (* Expected result: [4, 5, 5, 6] *)
value "sortsums [1,2,3] [1000,100,10]"  (* Expected result: [11, 12, 13, 101, 102, 103, 1001, 1002, 1003] *)

(* Lemma: Sorting preserves the length of the list *)
lemma sorted_size_preserved:
  shows "length (sort (pairwise_sums xs ys)) = length (pairwise_sums xs ys)"
  by auto

(* Lemma: sortsums returns a sorted list *)
lemma sortsums_sorted:
  shows "sorted (sortsums xs ys)"
  unfolding sortsums_def
  apply auto
  done

(* Lemma: The length of the result is the product of the lengths of the input lists *)
lemma sortsums_size:
  shows "length (sortsums xs ys) = length xs * length ys"
  unfolding sortsums_def
  apply (induct xs)
  apply auto
  done

(* Lemma: Proving O(n^2) complexity in terms of length *)
lemma sortsums_complexity: 
  fixes xs ys :: "int list"
  shows "length (sortsums xs ys) = length xs * length ys"
  by (simp add: sortsums_size)
 
theorem sorting_pairwise_sums_correct:
  "sorted (sortsums xs ys) \<and> length (sortsums xs ys) = length xs * length ys"
  by (simp add: sortsums_sorted sortsums_size)

(*<---------------------- Lambert’s algorithm ---------------------->*)

definition negate :: "int \<Rightarrow> int" where
  "negate x = - x"

definition operation_negate :: "int \<Rightarrow> int \<Rightarrow> int" ("\<ominus>") where
  "\<ominus> x y = \<oplus> x (negate y)"

(* Generate a list of indices with the same length as the list xs *)
definition zip_with_indices :: "int list \<Rightarrow> (int \<times> nat) list" where
  "zip_with_indices xs = zip xs (upt 1 (length xs + 1))"

value "zip_with_indices [5,6,7]"  (* Expected result: [(5,1), (6,2), (7,3)] *)


(* Function that generates a list of pairs with indices and subs their values *)
fun subs :: "int list \<Rightarrow> int list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "subs [] _ = []"
| "subs _ [] = []"
| "subs xs ys=
        concat(
                        map (
                               \<lambda> (x, i). 
                              map (
                                    \<lambda> (y, j). 
                                    (\<ominus> x y, (i, j))) 
                                    (zip_with_indices ys)) 
                              (zip_with_indices xs)
                )"

value "subs [7, 12] [4, 6]"  (* Expected result: [(3, (1, 1)), (1, (1, 2)), (8, (2, 1)), (6, (2, 2))] *)

(* General merge function that accepts a comparison function *)
fun merge :: "('a::ord \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
  where
    "merge [] ys = ys" |
    "merge xs [] = xs" |
    "merge (x#xs) (y#ys) = (if fst x \<le> fst y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

(* Divide and Conquer method for sorting the subs using  merge *)
fun sortsubs' :: "(int \<times> (nat \<times> nat)) list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "sortsubs' [] = []" |
  "sortsubs' [x] = [x]" |
  "sortsubs' xs = (
    let mid = length xs div 2;
        left = take mid xs;
        right = drop mid xs
    in merge (sortsubs' left) (sortsubs' right)
  )"

(* Sorting the subs *)
definition sortsubs :: "int list \<Rightarrow> int list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "sortsubs xs ys = sortsubs' (subs xs ys)"

value "sortsubs [7, 12] [4, 6]"            (* Expected result: [(1, (1, 2)), (3, (1, 1)), (6, (2, 2)), (8, (2, 1))] *)
value "map fst (sortsubs [7, 12] [4, 6])"  (* Expected result: [1, 3, 6, 8] *)

(* Lemma: Sorting preserves the length of the list *)
lemma sorted_size_preserved2[simp]:
  shows "length (sortsubs xs ys) = length (subs xs ys)"
  proof -
  have "sortsubs xs ys = sortsubs' (subs xs ys)"
    by (simp add: sortsubs_def)
  then show ?thesis
    by (induction "subs xs ys" rule: sortsubs'.induct, auto)
qed

(* Lemma: sortsubs returns a sorted list *)
lemma sortsubs_sorted[simp]:
  shows "sorted (map fst (sortsubs xs ys))"
  proof -
  have "sortsubs xs ys = sortsubs' (subs xs ys)"
    by (simp add: sortsubs_def)
  then show ?thesis
  by (induction "subs xs ys" rule: sortsubs'.induct, auto)
qed

(* Lemma: The length of the result is the product of the lengths of the input lists *)
lemma sortsubs_size[simp]:
  shows "length (sortsubs xs ys) = length xs * length ys"
 proof -
  have "length (subs xs ys) = length xs * length ys"
    by (induction "subs xs ys" rule: sortsubs'.induct, auto)
  thus ?thesis
    by auto
    qed
    
(*<----------------------------------------------------------------->*)

value "sortsums [5,6,7] [10,20,30]"                         (* Expected result: [15, 16, 17, 25, 26, 27, 35, 36, 37] *)
value " map fst (sortsubs [5,6,7] (map negate [10,20,30]))" (* Expected result: [15, 16, 17, 25, 26, 27, 35, 36, 37] *)

(*TODO*)
(* Lemma: sortsums is equivalent to sorting subs with negation *)
lemma sortsums_sortsubs:
  shows "sortsums xs ys = map fst (sortsubs xs (map negate ys))"
  sorry
  
(*<----------------------------------------------------------------->*)

type_synonym n3 = "(nat \<times> nat \<times> nat)"

(* Merging two sorted lists with tags *)
fun tag :: "nat \<Rightarrow> (int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> n3)"
  where "tag i (x, (j, k)) = (x, (i, j, k))"

fun table :: "int list \<Rightarrow> int list \<Rightarrow> (nat \<times> nat \<times> nat) list"
  where "table xs ys = map snd (merge (map (tag 1) (sortsubs xs xs)) (map (tag 2) (sortsubs ys ys)))"

  
(*<---------------------------- mkArray ---------------------------->*)

(*
mkArray xs ys = array b (zip (table xs ys) [1..])
                where b = ((1, 1, 1), (2, p, p))
                      p = max (length xs) (length ys)
*)

definition p :: "int list \<Rightarrow> int list \<Rightarrow> nat" where
  "p xs ys = max (length xs) (length ys)"

definition mkArray_bounds :: "int list \<Rightarrow> int list => (n3 \<times> n3)" where
  "mkArray_bounds xs ys = ((1,1,1),(2,(p xs ys),(p xs ys)))"
  
definition mkArray_zip :: "int list \<Rightarrow> int list \<Rightarrow> (n3 \<times> nat) list" where
  "mkArray_zip xs ys = zip (table xs ys) (map Suc (upt 0 (length (table xs ys))))"

value "table [1,2,3] [4,5]"
value "mkArray_bounds [1,2,3] [4,5]"
value "mkArray_zip [1,2,3] [4,5]"

(* Function that checks if (x, y, z) is within bounds *)
fun in_bounds :: "n3 \<Rightarrow> n3 \<Rightarrow> n3 \<Rightarrow> bool" where
  "in_bounds (low1, low2, low3) (high1, high2, high3) (x, y, z) =
    (low1 \<le> x \<and> x \<le> high1 \<and>
     low2 \<le> y \<and> y \<le> high2 \<and>
     low3 \<le> z \<and> z \<le> high3)"

(* Auxiliary function that filters the list *)
fun filter_in_bounds :: "n3 \<times> n3 \<Rightarrow> (n3 \<times> nat) list \<Rightarrow> (n3 * nat) list" where
  "filter_in_bounds bounds [] = []" |
  "filter_in_bounds bounds (((x, y, z), v) # xs) =
     (if in_bounds (fst bounds) (snd bounds) (x, y, z) then ((x, y, z), v) # filter_in_bounds bounds xs
      else filter_in_bounds bounds xs)"

(* Auxiliary function for comparing two elements of type (nat * nat * nat) *)
fun compare_tuples :: "n3 \<Rightarrow> n3 \<Rightarrow> bool" where
  "compare_tuples (x1, y1, z1) (x2, y2, z2) = (if x1 < x2 then True else if x1 = x2 then (if y1 < y2 then True else if y1 = y2 then z1 \<le> z2 else False) else False)"

(* Function for sorting the list *)
fun sort_array :: "(n3 \<times> nat) list \<Rightarrow> (n3 \<times> nat) list" where
  "sort_array [] = []" |
  "sort_array (x#xs) = sort_array [y \<leftarrow> xs. compare_tuples (fst y) (fst x)] @ [x] @ sort_array [y \<leftarrow> xs. \<not>compare_tuples (fst y) (fst x)]"

(* The main mkArray function *)
fun mkArray :: "int list \<Rightarrow> int list \<Rightarrow> (n3 \<times> nat) list" where
  "mkArray xs ys = sort_array (filter_in_bounds (mkArray_bounds xs ys) (mkArray_zip xs ys))"
  
(* Testing the mkArray function with inputs *)
value "mkArray_bounds [1,2,3] [4,5]"
value "mkArray_zip [1,2,3] [4,5]"
value "mkArray [1,2,3] [4,5]"

(*<----------------------------------------------------------------->*)
(*
The conversion of a list to a map using map_of has complexity O(n).
After that, each access to an element in the map has constant complexity O(1).

sortsubs2 xs ys = sortBy (cmp (mkArray xs ys)) (subs xs ys)
cmp a (x,(i,j)) (y,(k,l))
              = compare (a!(1,i,k)) (a!(2,j,l))
*)
value "map_of (mkArray [1,2,3] [4,5])"

fun indexing :: "(n3 \<Rightarrow> nat option) \<Rightarrow> n3 \<Rightarrow> nat" (infix "!!" 105) where
  "a !! idx = the (a idx)"

datatype ordering = LT | EQ | GT

fun compare :: "nat \<Rightarrow> nat \<Rightarrow> ordering" where
  "compare x y = (if x \<le> y then LT else if x > y then GT else EQ)"

fun cmp' :: "(n3 \<Rightarrow> nat option) \<Rightarrow> int \<times> nat \<times> nat \<Rightarrow> int \<times> nat \<times> nat \<Rightarrow> ordering" where
  "cmp' a (x,(i,j)) (y,(k,l)) = compare (a !! (1,i,k)) (a !! (2,j,l))"

fun cmp :: "(n3 \<times> nat) list \<Rightarrow> int \<times> nat \<times> nat \<Rightarrow> int \<times> nat \<times> nat \<Rightarrow> ordering" where
  "cmp a (x,(i,j)) (y,(k,l)) = cmp' (map_of a) (x,(i,j)) (y,(k,l))"
  
value "indexing (map_of (mkArray [1,2,3] [4,5])) (1, 3, 1)"
value "(map_of (mkArray [1,2,3] [4,5])) !! (1, 3, 1)"
value "cmp (mkArray [1,2,3] [4,5]) (2, 1, 2) (2, 1, 2) "
value "mkArray [1,2,3] [4,5]"

fun insert :: "(n3 \<times> nat) list \<Rightarrow> (int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> (nat \<times> nat)) list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "insert a x [] = [x]" |
  "insert a x (y#ys) = (if cmp a x y = LT then x # y # ys else y # insert a x ys)"

fun sortsubs2_manual :: "(n3 \<times> nat) list \<Rightarrow> (int \<times> (nat \<times> nat)) list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "sortsubs2_manual a [] = []" |
  "sortsubs2_manual a (x#xs) = insert a x (sortsubs2_manual a xs)"

fun sortsubs2 :: "int list \<Rightarrow> int list \<Rightarrow> (int \<times> (nat \<times> nat)) list" where
  "sortsubs2 xs ys = sortsubs2_manual (mkArray xs ys) (subs xs ys)"

value "sortsubs [1,2,3] [4,5]"  (* Expected result: [(- 4, 1, 2), (- 3, 1, 1), (- 3, 2, 2), (- 2, 2, 1), (- 2, 3, 2), (- 1, 3, 1)]*)
value "sortsubs2 [1,2,3] [4,5]" (* Expected result: [(- 4, 1, 2), (- 3, 1, 1), (- 3, 2, 2), (- 2, 2, 1), (- 2, 3, 2), (- 1, 3, 1)]*)

(*TODO*)
lemma sorstubs_sortsubs2:
  shows "sortsubs xs ys = sortsubs2 xs ys"
  sorry

(*<----------------------- Divide and conquer ----------------------->*)

fun incr :: "nat \<Rightarrow> (int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> (nat \<times> nat))" where
  "incr m (x, (i, j)) = (x, (i, m + j))"

fun incl :: "nat \<Rightarrow> (int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> (nat \<times> nat))" where
  "incl m (x, (i, j)) = (x, (m + i, j))"

fun incb :: "nat \<Rightarrow> (int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> (nat \<times> nat))" where
  "incb m (x, (i, j)) = (x, (m + i, m + j))"

fun switch :: "(int \<times> (nat \<times> nat)) \<Rightarrow> (int \<times> (nat \<times> nat))" where
  "switch (x, (i, j)) = (negate x, (j, i))"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) = reverse xs @ [x]"
  
value "sortsubs [1,2,3] [4,5]"
value "reverse (sortsubs [1,2,3] [4,5])"

(*FIXME*)
(* sortsubs ys xs = map switch (reverse (sortsubs xs ys)) *)
value "map switch (reverse (sortsubs [1,2,3] [4,5]))" (* Result1: [(1, 1, 3), (2, 2, 3), (2, 1, 2), (3, 2, 2), (3, 1, 1), (4, 2, 1)] *)
value "sortsubs [4,5] [1,2,3]"                        (* Result2: [(1, 1, 3), (2, 1, 2), (2, 2, 3), (3, 1, 1), (3, 2, 2), (4, 2, 1)] *)

lemma sortsubs_switch_negate:
  shows "sortsubs ys xs = map switch (reverse (sortsubs xs ys))"
  sorry

end