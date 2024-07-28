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

(* dokazivanje lema *)

lemma checklist_correct:
  assumes "set xs ⊆ {0..<length xs + 1}"
  shows "∀i < length xs + 1. (checklist xs) ! i = (i ∈ set xs)"
proof -
  have "checklist xs = map (\<lambda>i. i ∈ set xs) [0..<length xs + 1]" by simp
  thus "∀i < length xs + 1. (checklist xs) ! i = (i ∈ set xs)" by simp
qed

lemma minfree_correct:
  assumes "set xs ⊆ {0..<length xs + 1}"
  shows 
"minfree xs ∈ {0..<length xs + 1} ∧ minfree xs ∉ set xs ∧ (∀m < minfree xs. m ∈ set xs)"
proof -
  obtain n where n_def: "n = minfree xs" by simp
  have "n ∉ set xs ∧ (∀m < n. m ∈ set xs)" using someI_ex by auto
  thus ?thesis using assms by auto
qed


lemma minfree_combined_correct:
  assumes "set xs ⊆ {0..<length xs + 1}"
  shows "minfree_combined xs = minfree xs"
proof -
  have "∀i < length xs + 1. (checklist xs) ! i = (i ∈ set xs)" using checklist_correct assms by simp
  hence "search (checklist xs) = minfree xs" using minfree_correct assms by auto
  thus ?thesis by (simp add: minfree_combined_def)
qed


lemma search_correct:
  assumes "length xs > 0"
  shows "(∃n < length xs. xs ! n = False) ⟹ xs ! (search xs) = False ∧ (∀i < search xs. xs ! i = True)"
proof (induction xs rule: search.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case
  proof (cases x)
    case True
    then have IH: "(∃n < length xs. xs ! n = False) ⟹ xs ! (search xs) = False ∧ (∀i < search xs. xs ! i = True)"
      using "2.IH" by simp
    hence "search (x # xs) = 1 + search xs" by (simp add: True)
    thus ?thesis
    proof-
      assume "∃n < length xs. xs ! n = False"
      then obtain n where "n < length xs" and "xs ! n = False" by auto
      hence "(x # xs) ! (1 + search xs) = False ∧ (∀i < 1 + search xs. (x # xs) ! i = True)"
        using IH by simp
      thus "(x # xs) ! (search (x # xs)) = False ∧ (∀i < search (x # xs). (x # xs) ! i = True)"
        using True by simp
    qed
  next
    case False
    thus ?thesis by simp
  qed
qed


(* Test primeri *)
value "minfree_combined [0::nat, 2, 4, 5]"
value "minfree_combined [0::nat,1, 2, 4, 5]"

end
