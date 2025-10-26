theory UnravellingGreedyAlgorithms
  imports Main
begin


(* I Specification *)

(* minBy je u knjizi nedeterministička funkcija definisana tako da vraća neku vrednost za koju važi:
     minBy f xs \<in> xs \<and> (\<forall>x \<in> xs : f (minBy f xs) \<le> f x )
   
   Dalje se koristi refinement operator (f \<leadsto> g) koji označava da za svako x, deterministicka
   funkcija g x vraća vrednost koja je moguća vrednost nedeterminističke funkcije f x.

   Nisam bio siguran kako to da implementiram u Izabelu pa sam nedetrminističke funkcije iz knjige
   predstavio kao funkcije koje vraćaju skup svih mogućih vrednosti.
*)
definition minBy :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a set"  where
  "minBy f xs \<equiv> {x. x \<in> set xs \<and> (\<forall>y \<in> set(xs) . f x \<le> f y) }"

definition refinement :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" (infixl "\<leadsto>" 100) where
  "f \<leadsto> g \<longleftrightarrow> (\<forall>x. g x \<in> f x)"

primrec prefixes :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list list" where
  "prefixes x [] = [[[x]]]"
| "prefixes x (xs # xss) = [(x # xs) # xss] @ map ((#) xs) (prefixes x xss)"

(* List.maps ima isto znacenje kao concatMap u haskelu *)
definition unravels :: "'a list \<Rightarrow> 'a list list list" where
  "unravels xs = foldr (List.maps \<circ> prefixes) xs [[]]"

definition all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "all f xs = (\<forall>x\<in>(set xs). f x)"

fun up :: "'a::linorder list \<Rightarrow> bool" where
  "up [] = True"
| "up [x] = True"
| "up (x # (y # xs)) = (x \<le> y \<and> up (y # xs))"


(* Ovo je takođe nedeterministička funkcija i predstavlja specifikaciju funkcije supravel *)
definition supravel_nd :: "('a::linorder list \<Rightarrow> 'a list list set)" where
  "supravel_nd \<equiv> (minBy length \<circ> filter (all up) \<circ> unravels)"


(* II Derivation *)

fun head :: "'a list \<Rightarrow> 'a" where
  "head (x # xs) = x"

primrec uprefixes :: "'a::linorder \<Rightarrow> 'a list list \<Rightarrow> 'a list list list" where
  "uprefixes x [] = [[[x]]]"
| "uprefixes x (xs # xss) = (if x \<le> head xs
                               then [(x # xs) # xss] @ map ((#) xs) (uprefixes x xss)
                               else map ((#) xs) (uprefixes x xss))"

definition upravels :: "'a::linorder list \<Rightarrow> 'a list list list" where
  "upravels xs = foldr (List.maps \<circ> uprefixes) xs [[]]"

lemma unravels_upravels: "filter (all up) \<circ> unravels = upravels"
  sorry


definition heads :: "'a::linorder list list \<Rightarrow> 'a list" where
  "heads = sort \<circ> map head"

fun order1 :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<unlhd>" 100) where
  "[] \<unlhd> _ \<longleftrightarrow> True"
| "(x # xs) \<unlhd> (y # ys) \<longleftrightarrow> x \<ge> y \<and> xs \<unlhd> ys"
| "(x # xs) \<unlhd> [] \<longleftrightarrow> False"

definition order2 :: "'a::linorder list list \<Rightarrow> 'a list list \<Rightarrow> bool" (infixl "\<preceq>" 100) where
  "ur \<preceq> vr \<longleftrightarrow> heads ur \<unlhd> heads vr"

definition minWith :: "('a::linorder list list \<Rightarrow> 'a list list \<Rightarrow> bool) \<Rightarrow> 'a list list list \<Rightarrow> 'a list list set"  where
  "minWith order urs \<equiv> {x. x \<in> set urs \<and> (\<forall>ur \<in> set urs . (order x ur))}"

lemma minWith_minBy: "minWith (\<preceq>) x \<subseteq> minBy length x"
  unfolding order2_def minWith_def minBy_def
  sorry

(* (8.2) iz knjige *)
(* Ime insert je zauzeto pa koristimo insert' *)
lemma monotonicity_8_2: "((minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x) \<longrightarrow> (ur \<preceq> vr \<longrightarrow> insert' x ur \<preceq> insert' x vr)"
  unfolding minWith_def order2_def refinement_def
  sorry

(* Redosled argumenata foldr se razlikuje u Izabelu i Haskelu pa ovo moram da zapišem drugačije nego u knjizi. *)
lemma foldr_insert: "((minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x) \<longrightarrow> (\<forall>z. foldr insert' z [] \<in> (minWith (\<preceq>) \<circ> upravels) z)"
  sorry

primrec insert' :: "'a::ord \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "insert' x [] = [[x]]"
| "insert' x (xs # xss) = (if x \<le> head xs then (x # xs) # xss
                                         else xs # insert' x xss)"

lemma insert_correct: "(minWith (\<preceq>) \<circ> uprefixes x) \<leadsto> insert' x"
  sorry

(* Finalno rešenje *)
definition supravel :: "'a::linorder list \<Rightarrow> 'a list list" where
  "supravel x = foldr insert' x []"

(* Dokaz korektnosti rešenja *)
lemma supravel_correct: "supravel_nd \<leadsto> supravel"
  unfolding supravel_def supravel_nd_def refinement_def
  using insert_correct unravels_upravels minWith_minBy foldr_insert
  sorry

end