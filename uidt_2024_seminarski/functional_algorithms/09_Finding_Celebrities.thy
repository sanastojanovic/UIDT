theory "09_Finding_Celebrities"
  imports Main
begin

(*Autor: Minja Popović
  Indeks: 39/2018
  Datum: 21.09.2024.*)

(*Predstavimo osobe prirodnim brojevima i definišimo skup ps*)
type_synonym person = nat
definition ps :: "person list" where
  "ps = [1,2,3,4,5]"

(*Radi primera, neka svi parni brojevi predstavljaju poznate ličnosti 
  (svi poznaju parne, dok su neparni poznati samo sami sebi i neparnima manjim od njih)*)
definition knows :: "person \<Rightarrow> person \<Rightarrow> bool" where
  "knows p q = (if even q then True
                else odd p \<and> p \<le> q)"

(*Definicija celebrity clique-a*)
(*Napomena: Koristimo liste bez duplikata umesto skupova radi lakšeg korišćenja nekih f-ja kasnije*)
definition is_celebrity_clique :: "person list  \<Rightarrow> person list  \<Rightarrow> bool" where
  "is_celebrity_clique P C \<equiv> (
    C \<noteq> [] \<and>
    (\<forall>x \<in> set P. \<forall>y \<in> set C. knows x y) \<and>
    (\<forall>x \<in> set P. \<forall>y \<in> set C. knows y x \<longrightarrow> x \<in> set C)
  )"

value "is_celebrity_clique ps [2]"
value "is_celebrity_clique ps [2,4]"
value "is_celebrity_clique ps [2,3,4]"

(*Pomoćna funkcija za generisanje podskupova/podlisti*)
fun subseqs :: "person list \<Rightarrow> person list list" where
  "subseqs [] = [[]]" |
  "subseqs (x # xs) = (map (\<lambda>ys. x # ys) (subseqs xs)) @ (subseqs xs)"

value "subseqs [1,2,3]"

(*Naivno rešenje filtriranja podskupova na osnovu definicije*)
definition cclique :: "person list \<Rightarrow> person list" where
  "cclique P = (
    let valid_cliques = filter (is_celebrity_clique P) (subseqs P)
    in (if valid_cliques = [] then [] else hd valid_cliques )
  )"

value "cclique ps"

(*Generatorska funkcija*)
primrec cclique_gen :: "person \<Rightarrow> person list \<Rightarrow> person list" where
  "cclique_gen p [] = [p]" |
  "cclique_gen p (c # cs) = (
    if (\<not>(knows p c)) then [p]
    else if (\<not>(knows c p)) then (c # cs) 
    else p # (c #cs)
  )"

value "cclique_gen 6 []"
value "cclique_gen 6 ps"
value "cclique_gen 7 (cclique ps)"
value "cclique_gen 6 (cclique ps)"

(*Rešenje linearne složenosti uz korišćenje generatorske funkcije*)
definition cclique_opt :: "person list \<Rightarrow> person list" where
  "cclique_opt P = (if P = [] then [] else foldr cclique_gen P [])"

value "cclique_opt ps"

(*Pomoćne leme za dokaz validnosti cclique_opt*)
lemma cclique_addition: 
  shows "cclique (p # P) = cclique_gen p (cclique P)"
proof (induction P)
  case Nil
  have "is_celebrity_clique [p] [p]" unfolding is_celebrity_clique_def knows_def by auto
  then show ?case unfolding cclique_def cclique_gen_def by auto
next
  case (Cons q Q)
  show ?case
    sorry
qed

lemma cclique_opt_addition: "cclique_gen p (cclique_opt P) = cclique_opt (p # P)"
  unfolding cclique_opt_def by auto

(*Dokaz validnosti cclique_opt*)
theorem cclique_opt_validity:
  assumes "cclique P \<noteq> []"
  shows "cclique P = cclique_opt P"
proof (induction P)
  case Nil
  then show ?case unfolding cclique_opt_def cclique_def by auto
next
  case (Cons p P)
  have "cclique (p # P) = cclique_gen p (cclique P)"  using cclique_addition by auto
  also have "... = cclique_gen p (cclique_opt P)" using Cons by auto
  also have "... = cclique_opt (p # P)" using cclique_opt_addition by auto
  finally show ?case .
qed

end