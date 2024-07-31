
(*author: Todor Todorovic *)
theory Smallest_Free_Number
  imports Main
begin

(* Pomoćna funkcija za pronalaženje najmanjeg prirodnog broja koji nije u listi *)
fun minfree_aux :: "nat list => nat => nat" where
"minfree_aux [] n = n" |
"minfree_aux (x#xs) n = (if n = x then minfree_aux xs (Suc n) else minfree_aux xs n)"

fun minfree :: "nat list => nat" where
"minfree xs = minfree_aux (sort xs) 0"

(* Funkcija za razliku *)
fun diff :: "nat list => nat list => nat list" where
"diff [] ys = []" |
"diff (x#xs) ys = (if x ∈ set ys then diff xs ys else x # diff xs ys)"

(* Funkcija za proveru liste *)
fun checklist :: "nat list => (nat => bool)" where
"checklist xs = (%n. n < length xs & n ∈ set xs)"

(* Dokazi lema *)

lemma minfree_aux_n_not_in_set: 
  "sorted xs ⟹ n ∉ set xs ⟹ minfree_aux xs n = n"
  apply (induct xs arbitrary: n)
   apply auto
  done

lemma minfree_aux_n_in_set: 
  "sorted xs ⟹ n ∈ set xs ⟹ minfree_aux xs n = minfree_aux xs (Suc n)"
  apply (induct xs arbitrary: n)
   apply auto
  done

lemma minfree_aux_correct:
  "sorted xs ⟹ minfree_aux xs n = (LEAST k. k ≥ n ∧ k ∉ set xs)"
  apply (induct xs arbitrary: n)
   apply auto
  subgoal for x xs n
    apply (cases "n = x")
     apply (simp add: minfree_aux_n_in_set minfree_aux_n_not_in_set Least_Suc)
    subgoal
      apply (rule Least_equality)
       apply (auto)
      done
    done
  done

lemma minfree_correct: "minfree xs = (LEAST n. n ∉ set xs)"
  apply (simp add: minfree_aux_correct)
  done

lemma diff_correct: "diff xs ys = [x <- xs. x ∉ set ys]"
  apply (induct xs)
   apply auto
  done

lemma checklist_correct: "∀n. (checklist xs n) = (n < length xs & n ∈ set xs)"
  apply (induct xs)
   apply auto
  done

(* Test primeri *)
value "minfree [0, 1, 2, 4, 5]" (* Očekivani rezultat: 3 *)
value "minfree [1, 2, 3, 4, 5]" (* Očekivani rezultat: 0 *)
value "minfree [0, 2, 3, 4, 5]" (* Očekivani rezultat: 1 *)

value "diff [1, 2, 3, 4, 5] [2, 4]" (* Očekivani rezultat: [1, 3, 5] *)
value "diff [1, 2, 2, 3, 4, 5] [2, 4]" (* Očekivani rezultat: [1, 3, 5] *)

value "checklist [0, 1, 2, 3, 4] 2" (* Očekivani rezultat: True *)
value "checklist [0, 1, 2, 3, 4] 5" (* Očekivani rezultat: False *)

end
