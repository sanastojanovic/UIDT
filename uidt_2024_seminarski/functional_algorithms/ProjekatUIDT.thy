theory ProjekatUIDT

imports Main

begin

fun unija :: "nat list ⇒ nat list ⇒ nat list" where
  "unija xs [] = xs"
| "unija [] ys = ys"
| "unija (x#xs) (y#ys) = (if x<y then x#unija xs (y#ys)                                            
                          else if y<x then y#unija (x # xs) ys
                          else x # unija xs ys)"


fun smallest :: "nat ⇒ nat list ⇒ nat" where
  "smallest k xs = xs ! k"
value "unija [2, 4, 5, 6] [2, 4, 5, 7, 9]"
value "smallest 3 (unija [2, 4, 5, 6] [2, 4, 5, 7, 9])"

primrec sortirana :: "nat list ⇒ bool" where
  "sortirana [] ⟷ True"
| "sortirana (x # xs) ⟷ sortirana xs ∧ (∀ a ∈ set xs . x ≤ a)"

primrec sadrzi :: "nat ⇒ nat list ⇒ bool" where
  "sadrzi a [] ⟷ False"
| "sadrzi a (x # xs) = (a = x ∨ sadrzi a xs)"

primrec razliciti :: "nat list ⇒ bool" where
  "razliciti [] ⟷ True"
| "razliciti (x # xs) ⟷ (¬ (sadrzi x xs) ∧ razliciti xs)"


lemma set_unija:
  shows "set (unija xs ys) = set xs ∪ set ys"
  apply(induction xs ys rule: unija.induct)
    apply auto
  done

lemma sorted_spoji:
  assumes "sortirana xs" "sortirana ys"
  shows "sortirana (unija xs ys)"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply (auto simp add: set_unija)
  done

lemma unija_append:
  shows "(∀ x ∈ set xs. ∀ y ∈ set ys. x < y) ⟹ xs @ ys = unija xs ys"
  apply(induction xs ys rule: unija.induct)
    apply auto
  done

lemma k_manje_duzina_xs:
  assumes "unija xs ys = xs @ ys"
  shows " k < length xs ⟹ smallest k (unija xs ys) = smallest k xs"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply auto
  apply(induction k)
   apply auto
  by (meson nth_append_left)
  

lemma k_vece_duzina_xs:
  assumes "unija xs ys = xs @ ys"
  shows " k ≥ length xs ⟹ smallest k (unija xs ys) = smallest (k-length xs) ys"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply auto
   apply(induction k)
    apply auto
  apply (metis append.right_neutral nth_append_right)
  apply(induction k)
   apply auto
  using nth_append_right by blast
      (*[xs] [us] [vs] [ys]   *)

primrec disjunktne :: "nat list ⇒ nat list ⇒ bool" where
  "disjunktne [] ys ⟷ True"
| "disjunktne (x # xs) ys ⟷ sadrzi x ys ∧ disjunktne xs ys"

lemma union_concat:
  assumes "sorted (xs @ ys)" "sorted (us @ vs)"
      and "disjunktne (xs @ ys) (us @ vs) ⟷ True" 
      and "disjunktne xs ys ⟷ True" "disjunktne us vs ⟷ True"
      and "unija xs vs = xs @ vs" "unija us ys = us @ ys"
  shows "unija (xs @ ys) (us @ vs) = (unija xs us) @ (unija ys vs)"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply auto
    apply(induction us vs rule: unija.induct)
      apply auto
  apply (metis Cons_eq_appendI disjunktne.simps(2) neq_Nil_conv
      sadrzi.simps(1) unija.simps(2))
  apply (metis append_Cons disjunktne.simps(2) list.exhaust sadrzi.simps(1)
      unija.simps(2))
    apply(induction us vs rule: unija.induct)
      apply auto
              apply (metis disjunktne.simps(2) neq_Nil_conv sadrzi.simps(1))
  sorry
 

end
