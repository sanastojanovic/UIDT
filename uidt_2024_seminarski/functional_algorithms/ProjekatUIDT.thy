theory ProjekatUIDT

imports Main

begin
fun unija :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "unija xs [] = xs"
| "unija [] ys = ys"
| "unija (x#xs) (y#ys) = (if x<y then x#unija xs (y#ys)                                            
                          else if x>y then y#unija (x # xs) ys
                          else x#unija xs ys)"


definition smallest :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "smallest k xs = xs ! k"

value "unija [2, 4, 5, 6] [2, 4, 5, 7, 9]" 
(*[2, 4, 5, 6, 7, 9]  ako su pocetne liste sortirane sortira i izbaca duplikate*)
value "smallest 3 (unija [2, 4, 5, 6] [2, 4, 5, 7, 9])"  (* [2, 4, 5, 6, 7, 9] ! 3 = 6*)

primrec sortirana :: "nat list \<Rightarrow> bool" where
  "sortirana [] \<longleftrightarrow> True"
| "sortirana (x # xs) \<longleftrightarrow> sortirana xs \<and> (\<forall> a \<in> set xs . x \<le> a)"

value "sortirana [1, 2, 3, 4]"
value "sortirana [2, 3, 1, 4]"

primrec sadrzi :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "sadrzi a [] \<longleftrightarrow> False"
| "sadrzi a (x # xs) = (a = x \<or> sadrzi a xs)"

value "sadrzi 3 [1, 2, 3]" 
value "sadrzi 1 [2, 3, 4]"

lemma sadrzi_a_in_set:
  shows "sadrzi a xs \<longleftrightarrow> a \<in> set xs"
  apply(induction xs)
   apply auto
  done

primrec razliciti :: "nat list \<Rightarrow> bool" where
  "razliciti [] \<longleftrightarrow> True"
| "razliciti (x # xs) \<longleftrightarrow> (\<not> (sadrzi x xs) \<and> razliciti xs)"

value "razliciti [1, 2, 3, 4, 5]"
value "razliciti [1, 2, 3, 3, 5]"

lemma set_unija:
  shows "set (unija xs ys) = set xs \<union> set ys"
  apply(induction xs ys rule: unija.induct)
    apply auto
  done

lemma unija_jedinstven_raspored:  (*pokusaj da se ubaci neko predznanje za kasnije lemme*)
  assumes "sorted xs" "sorted ys"
  shows "unija xs ys = unija ys xs"
  apply(induction xs ys rule: unija.induct)
    apply auto
  by (metis neq_Nil_conv unija.simps(1,2))

lemma sorted_spoji: (*pokusaj da se ubaci neko predznanje za kasnije lemme*)
  assumes "sortirana xs" "sortirana ys"
  shows "sortirana (unija xs ys)"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply (auto simp add: set_unija)
  done

lemma unija_append:
  shows "(\<forall> x \<in> set xs. \<forall> y \<in> set ys. x < y) \<Longrightarrow> xs @ ys = unija xs ys"
  apply(induction xs ys rule: unija.induct)
    apply auto
  done

lemma k_manje_duzina_xs: (*dokaz 4.1 iz knjige*)
  assumes "unija xs ys = xs @ ys"
  shows " k < length xs \<Longrightarrow> smallest k (unija xs ys) = smallest k xs"
  using assms
  unfolding smallest_def
  apply(induction xs ys rule: unija.induct)
    apply auto
  apply(induction k)
   apply auto
  by (meson nth_append_left)
  
lemma k_vece_duzina_xs: (*dokaz 4.1 iz knjige*)
  assumes "unija xs ys = xs @ ys"
  shows " k \<ge> length xs \<Longrightarrow> smallest k (unija xs ys) = smallest (k-length xs) ys"
  using assms
  unfolding smallest_def
  apply(induction xs ys rule: unija.induct)
    apply auto
   apply(induction k)
    apply auto
  apply (metis append.right_neutral nth_append_right)
  apply(induction k)
   apply auto
  using nth_append_right by blast
      (*[xs] [us] [vs] [ys]   *)

primrec disjunktne :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "disjunktne [] ys \<longleftrightarrow> True"
| "disjunktne (x # xs) ys \<longleftrightarrow> (\<not>sadrzi x ys) \<and> disjunktne xs ys"

value "disjunktne [1, 2, 3] [4, 5, 6]"
value "disjunktne [1, 2, 3] [2, 5]"


lemma disj[simp]: (*dokaz da disjunktne radi korektno*)
  shows "(set xs \<inter> set ys = {}) \<Longrightarrow> disjunktne xs ys"
  apply(induction xs)
   apply (auto simp add: sadrzi_a_in_set)
  done

lemma skup_pom: (*pokusaj da se ubaci neko predznanje za dokaz lemme 4.2*)
  assumes "sorted xs" "sorted ys" "sorted us" "sorted vs"
      and "\<forall>x \<in> set xs. \<forall>y \<in> set ys. x<y"
      and "\<forall>u \<in> set us. \<forall>v \<in> set vs. u<v"
      and "\<forall>x \<in> set xs. \<forall>v \<in> set vs. x<v"
      and "\<forall>u \<in> set us. \<forall>y \<in> set ys. u<y"
      and  "\<forall>xu \<in> set (xs @ us). \<forall>yv \<in> set (ys@vs). xu < yv"
      and "distinct (xs@ys@us@vs)"
    shows "\<forall>xu \<in> set (xs @ us). \<forall> yv \<in> set (ys @ vs). xu < yv"
  using assms
  apply(induction xs)
   apply auto
  done

lemma (*pokusaj dokaza 4.2 uz pomoc medjukoraka*)
  assumes "\<forall>xu \<in> set (xs @ us). \<forall>yv \<in> set (ys @ vs). xu < yv"
          "sorted xs" "sorted us" "sorted ys" "sorted vs"
          "\<forall> x \<in> set xs. \<forall> y \<in> set ys. x < y"
          "\<forall> u \<in> set us. \<forall>v \<in> set vs. u < v"
          "\<forall> x \<in> set xs. \<forall> v \<in> set vs. x < v"
          "\<forall> u \<in> set us. \<forall>y \<in> set ys. u < y "
          "sorted (xs @ ys)" "sorted (us @ vs)"
  shows "unija (xs @ ys) (us @ vs) = (unija xs us) @ (unija ys vs)"
  using assms
  apply(induction xs ys rule: unija.induct)
  apply(induction us vs rule: unija.induct)
      apply (metis append_self_conv unija.simps(1))
     apply (metis unija_append)
  sledgehammer
  sorry

lemma union_concat: (*neki drugi pokusaj dokaza 4.2*)
  assumes "sorted (xs @ ys)" "sorted (us @ vs)"
      and "distinct (xs @ ys @ us @ vs)"
      and "disjunktne (xs @ ys) (us @ vs)" 
      and "disjunktne xs ys" "disjunktne us vs"
      and "unija xs vs = xs @ vs" "unija us ys = us @ ys"
      and "\<forall> x \<in> set xs . \<forall> v \<in> set vs. x<v"
      and "\<forall> u \<in> set us . \<forall> y \<in> set ys. u<y"
      and "length xs>0" "length ys>0" "length us>0" "length vs>0"
  shows "(unija xs us) @ (unija ys vs) = unija (xs @ ys) (us @ vs)"
  using assms
  apply(induction xs ys rule: unija.induct)
    apply auto
  apply(induction us vs rule: unija.induct)
  apply argo
   apply meson
  sledgehammer
  sorry

lemma
  assumes "\<forall>x \<in> set xs . x < a" "\<forall>y \<in> set ys. a < y"
          "\<forall>u \<in> set us . u < b" "\<forall>v \<in> set vs. b < v"
          "a < b" "ys1@ys2 = ys" "\<forall>y \<in> set ys1. y<b" 
          "\<forall>u \<in> set us. \<forall>y \<in> set ys2. u < y"
          "k \<le> length (xs @ us)"
  shows "smallest k (unija (xs@[a]@ys) (us@[b]@vs)) = smallest k (unija (xs@[a]@ys) us)"
  using assms
  unfolding smallest_def
  apply(induction k)
   apply(induction xs ys rule: unija.induct)
     apply auto
     apply(induction a)
      apply(induction b)
       apply(induction us vs rule: unija.induct)
         apply(induction ys1 ys2 rule: unija.induct)
           apply simp
          apply simp
         apply blast
        apply blast
       apply blast
  sledgehammer
  sorry
  (*smallest k (unija (xs@[a]@ys) (us@[b]@vs)
                unija (xs@[a]@ys1@ys2) (us@[b]@vs)
               (unija (xs@[a]@ys1) us) @ (unija ys2 [b]@vs) // primena 4.2
            iz pp.    k \<le> |xs++us|    
             smallest k ( unija (xs@[a]@ys1) us))     
             smallest k (unija (xs@[a]@ys1 us) @ unija ys2 [])  
                         unija (xs@[a]@ys1@ys2) us  "zadrzava se ispravnost na osnovi pp ys2>us"
                         unija xs@[a]@ys us        kraj*)


end
