theory mi16208_Darko_Neskovic
  imports Main
begin

(* Tekst zadatka *)

text\<open>
    Dokazati da meu svaka tri razliqita cela broja postoje dva, recimo a i b, takva da je broj a^5*b^3 - a^3 * b^5 deljiv sa 10.
    \<close>




(* Pomocne funkcije *)

definition triRazlicitaBroja :: " int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "triRazlicitaBroja x y z \<longleftrightarrow> (x \<noteq> y & y \<noteq> z & x \<noteq> z)"

definition deljivSa10 :: "int \<Rightarrow> bool" where
  "deljivSa10 x \<longleftrightarrow> x mod 10 = 0"

(* Izraz koji pokusavamo da dokazemo da je deljiv sa deset u datim uslovima *)
definition d_Izraz :: "int \<Rightarrow> int \<Rightarrow> int" where 
  "d_Izraz x y = (x ^ 5)*(y ^ 3) - (x ^ 3)*(y ^ 5)" 

definition ispunjavaUslov :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "ispunjavaUslov x y \<longleftrightarrow> deljivSa10(d_Izraz x y)"

(* Koristimo za kraci zapis provere u dokazu *)
definition ispunjavaUslov2 :: "int \<Rightarrow> int \<Rightarrow> bool" where
 "ispunjavaUslov2 x y \<longleftrightarrow> deljivSa10(d_Izraz x y) | deljivSa10(d_Izraz y x)"

value "triRazlicitaBroja 1 2 3" (* True *)
value "deljivSa10 30" (* True *)
value "deljivSa10 42" (* False *)  
value "d_Izraz 2 3" (* -1080 *)
value "d_Izraz (-2) (-3)" (* -1080 *)
value "ispunjavaUslov 2 3" (* True *)


(* Pokazujemo da lema vazi kada je jedan od brojeva nula *)
lemma d_null [simp]:
  fixes x :: int
  fixes y :: int
  fixes z :: int
  assumes "triRazlicitaBroja x y z & x = 0"
  shows "ispunjavaUslov x y | ispunjavaUslov y z | ispunjavaUslov x z "
  sorry

(* d_Izraz x y \<equiv> d_Izraz (-x) (-y) *)
lemma d_eq1 [simp]:
  fixes x :: int
  fixes y :: int
  assumes "x \<noteq> y"
  shows "d_Izraz x y = d_Izraz (-x) (-y)"
  sorry

(* d_Izraz (-x) y \<equiv> - d_Izraz x y *)
lemma d_eq2 [simp]:
  fixes x :: int
  fixes y :: int
  assumes "x \<noteq> y"
  shows "d_Izraz (-x) y = (-1) * d_Izraz x y"
  sorry

lemma d_deljivoSa2 [simp]:
  shows "(d_Izraz x y) mod 2 = 0"
  sorry

lemma d_deljivoSa5 [simp]:
  fixes x :: int
  fixes y :: int
  fixes z :: int
  assumes "x \<in> {1, 2, 3, 4, 6, 7, 8, 9} 
        | y \<in> {1, 2, 3, 4, 6, 7, 8, 9}
        | z \<in> {1, 2, 3, 4, 6, 7, 8, 9}"
  assumes "triRazlicitaBroja x y z"
  shows " x \<in> {1, 4, 6, 9} & y \<in> {1, 4, 6, 9} 
        | x \<in> {1, 4, 6, 9} & z \<in> {1, 4, 6, 9}
        | y \<in> {1, 4, 6, 9} & z \<in> {1, 4, 6, 9}
        | x \<in> {2, 3, 7, 8} & y \<in> {2, 3, 7, 8} 
        | x \<in> {2, 3, 7, 8} & z \<in> {2, 3, 7, 8}
        | y \<in> {2, 3, 7, 8} & z \<in> {2, 3, 7, 8} "
  using assms
  sorry


lemma Dokaz: 
  fixes x y z :: int 
  assumes "triRazlicitaBroja x y z = true"
  shows "ispunjavaUslov2 x y
        |ispunjavaUslov2 x z
        |ispunjavaUslov2 y z 
  "
  using assms
  sorry



end
