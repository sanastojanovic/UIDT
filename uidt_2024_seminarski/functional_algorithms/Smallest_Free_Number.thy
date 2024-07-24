theory Smallest_Free_Number
  imports Main
begin
(*author: Todor Todorovic *)

(* Funkcija koja vraća najmanji slobodan broj *)
fun minfree :: "nat list \<Rightarrow> nat" where
  "minfree xs = (SOME n. n \<notin> set xs \<and> (\<forall>m < n. m \<in> set xs))"

(* Funkcija za generisanje liste koja pokazuje prisustvo brojeva *)
fun checklist :: "nat list \<Rightarrow> bool list" where
  "checklist xs = map (\<lambda>n. n \<in> set xs) (upt 0 (length xs + 1))"

(* Funkcija za pronalaženje pozicije prvog False elementa *)
fun search :: "bool list \<Rightarrow> nat" where
  "search [] = 0" |
  "search (x # xs) = (if x then 1 + search xs else 0)"

(* Kombinovana funkcija *)
definition minfree_combined :: "nat list \<Rightarrow> nat" where
  "minfree_combined xs = search (checklist xs)"

(* Leme za dokazivanje ispravnosti *)

lemma checklist_correct:
  assumes "set xs \<subseteq> {0..<length xs + 1}"
  shows "\<forall>i < length xs + 1. (checklist xs) ! i = (i \<in> set xs)"
  sorry

lemma search_correct:
  assumes "length xs > 0"
  shows "(\<exists>n < length xs. xs ! n = False) \<Longrightarrow> xs ! (search xs) = False \<and> (\<forall>i < search xs. xs ! i = True)"
  sorry

lemma minfree_correct:
  assumes "set xs \<subseteq> {0..<length xs + 1}"
  shows 
"minfree xs \<in> {0..<length xs + 1} \<and> minfree xs \<notin> set xs \<and> (\<forall>m < minfree xs. m \<in> set xs)"
  sorry
lemma minfree_combined_correct:
  assumes "set xs \<subseteq> {0..<length xs + 1}"
  shows "minfree_combined xs = minfree xs"
  sorry

(* Test primeri *)
value "minfree_combined [0::nat, 2, 4, 5]"
value "minfree_combined [0::nat,1, 2, 4, 5]"

end