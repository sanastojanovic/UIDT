theory mi17502_Dimitrije_Sekulic_2
  imports Main

begin
(*
  Rad sa matricama dimenzije 3x3
  * Definicija tipa mat3 za matricu dimenzije 3x3
  * Sabiranje dve matrica
  * Mnozenje dve matrice
  * Stepenovanje matrica
  * Dokazati da vazi: 
         ^n
    1 0 0      1  0 0
    0 1 0   =  0  1 0
    1 2 1      n 2n 1
  * Distributivnost matrica

http://alas.matf.bg.ac.rs/~vsrdjan/files/lazad.pdf  zadatak 5.8

*)
(*Definisianje tipa mat3*)
type_synonym mat3 = "nat \<times> nat \<times> nat
                   \<times> nat \<times> nat \<times> nat
                   \<times> nat \<times> nat \<times> nat"

(*sabiranje dve matrice*)
fun mat3_add :: "mat3 \<Rightarrow> mat3 \<Rightarrow> mat3" where
"mat3_add 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (b1, b2, b3, b4, b5, b6, b7, b8, b9) = 
    (a1+b1, a2+b2, a3+b3, a4+b4, a5+b5, a6+b6, a7+b7, a8+b8, a9+b9)
"
(*Provera racunajna sabiranja*)
value "mat3_add (1::nat, 2, 3, 4, 5, 6, 7, 8, 9) (1, 1, 1, 1, 1, 1, 1, 1, 1)"

(*Komutativnost sabiranja dve matrice*)
lemma mat3_add_kom[simp]:
 "mat3_add 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (b1, b2, b3, b4, b5, b6, b7, b8, b9) = 
  mat3_add 
     (b1, b2, b3, b4, b5, b6, b7, b8, b9)
      (a1, a2, a3, a4, a5, a6, a7, a8, a9)
"
  by auto

lemma mat3_add_kom_isar:
 "mat3_add 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (b1, b2, b3, b4, b5, b6, b7, b8, b9) = 
  mat3_add 
     (b1, b2, b3, b4, b5, b6, b7, b8, b9)
      (a1, a2, a3, a4, a5, a6, a7, a8, a9)"
proof-
  have "mat3_add 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (b1, b2, b3, b4, b5, b6, b7, b8, b9) = 
    (a1+b1, a2+b2, a3+b3, a4+b4, a5+b5, a6+b6, a7+b7, a8+b8, a9+b9)"
    by simp
  also have "... = (b1+a1, b2+a2, b3+a3, b4+a4, b5+a5, b6+a6, b7+a7, b8+a8, b9+a9)"
    by simp
  also have "... = mat3_add 
     (b1, b2, b3, b4, b5, b6, b7, b8, b9)
      (a1, a2, a3, a4, a5, a6, a7, a8, a9)"
    by simp
  finally show ?thesis
    by simp
qed

(*Sabiranje sa nultom matricom*)
lemma mat3_add_zero[simp]:
"mat3_add 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (0, 0, 0, 0, 0, 0, 0, 0, 0) = 
(a1, a2, a3, a4, a5, a6, a7, a8, a9)"
  by auto

(*Asocijativnost sabiranja*)
lemma mat3_add_asoc[simp]:
"mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) 
(mat3_add (b1, b2, b3, b4, b5, b6, b7, b8, b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)) = 
mat3_add (mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9))
 (c1, c2, c3, c4, c5, c6, c7, c8, c9)"
  by auto

(* A + (B + C) = (A + B) + C *)
lemma mat3_add_asoc_isar:
"mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) 
(mat3_add (b1, b2, b3, b4, b5, b6, b7, b8, b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)) = 
mat3_add (mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9))
 (c1, c2, c3, c4, c5, c6, c7, c8, c9)"
proof-
  have "mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) 
(mat3_add (b1, b2, b3, b4, b5, b6, b7, b8, b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)) = 
mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1+c1, b2+c2, b3+c3, b4+c4, b5+c5, b6+c6, b7+c7, b8+c8, b9+c9)"
    by simp
  also have "... = (a1+b1+c1, a2+b2+c2, a3+b3+c3, a4+b4+c4, a5+b5+c5, a6+b6+c6, a7+b7+c7, a8+b8+c8, a9+b9+c9)"
    by simp
  also have "... = mat3_add (a1+b1, a2+b2, a3+b3, a4+b4, a5+b5, a6+b6, a7+b7, a8+b8, a9+b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)"
    by simp
  also have "... = mat3_add (mat3_add (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9))
 (c1, c2, c3, c4, c5, c6, c7, c8, c9)"
    by simp
  finally show ?thesis
    by simp
qed

(*Mnozenje matrica*)
fun mat3_mul :: "mat3 \<Rightarrow> mat3 \<Rightarrow> mat3" where
"mat3_mul 
    (a1, a2, a3, a4, a5, a6, a7, a8, a9)
     (b1, b2, b3, b4, b5, b6, b7, b8, b9) = 
    (a1*b1+a2*b4+a3*b7, a1*b2+a2*b5+a3*b8, a1*b3+a2*b6+a3*b9,
     a4*b1+a5*b4+a6*b7, a4*b2+a5*b5+a6*b8, a4*b3+a5*b6+a6*b9,
     a7*b1+a8*b4+a9*b7, a7*b2+a8*b5+a9*b8, a7*b3+a8*b6+a9*b9)
"

(*Jedinicna matrica*)
definition eye3 :: mat3 where
"eye3 = (1, 0, 0, 0, 1, 0, 0, 0, 1)"

(*Test matrica*)
definition test_mat :: mat3 where
"test_mat = (1, 0, 0, 0, 1, 0, 1, 2, 1)"

value "mat3_mul test_mat eye3"

(*Mnozenje matrice sa jedinicnom*)
lemma mat3_mul_eye[simp]: 
"mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) eye3 = (a1, a2, a3, a4, a5, a6, a7, a8, a9)"
  by (simp add: eye3_def)

(*Stepen matrice*)
primrec mat3_pow :: "mat3 \<Rightarrow> nat \<Rightarrow> mat3" where
"mat3_pow A 0 = eye3" |
"mat3_pow A (Suc n) = mat3_mul A (mat3_pow A n)"

value "mat3_pow test_mat 5"

(*Dokazati da vazi: 
         ^n
    1 0 0      1  0 0
    0 1 0   =  0  1 0
    1 2 1      n 2n 1
*)
lemma zadatak:
"mat3_pow (1, 0, 0, 0, 1, 0, 1, 2, 1) n = (1, 0, 0, 0, 1, 0, n, 2*n, 1)"
  by (induction n, simp add: eye3_def) auto

lemma zadatak_isar:
"mat3_pow (1, 0, 0, 0, 1, 0, 1, 2, 1) n = (1, 0, 0, 0, 1, 0, n, 2*n, 1)"
proof(induction n)
case 0
  then show ?case 
    by (simp add: eye3_def)
next
  case (Suc n)
  have " mat3_pow (1, 0, 0, 0, 1, 0, 1, 2, 1) (Suc n) =
         mat3_mul (1, 0, 0, 0, 1, 0, 1, 2, 1) (mat3_pow (1, 0, 0, 0, 1, 0, 1, 2, 1) n)"
    by simp
  also have "... = mat3_mul (1, 0, 0, 0, 1, 0, 1, 2, 1) (1, 0, 0, 0, 1, 0, n, 2*n, 1)"
    using Suc
    by simp
  also have "... = (1, 0, 0, 0, 1, 0, Suc n, 2*(Suc n), 1)"
    by simp
  finally show ?case 
    by simp
qed

(*Distributivnost matrica A * (B + C) = A * B + A * C *)
lemma mat3_distr:
"mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) 
          (mat3_add (b1, b2, b3, b4, b5, b6, b7, b8, b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)) =
  mat3_add (mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9)) 
          (mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) (c1, c2, c3, c4, c5, c6, c7, c8, c9))"
proof-
  have "mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) 
          (mat3_add (b1, b2, b3, b4, b5, b6, b7, b8, b9) (c1, c2, c3, c4, c5, c6, c7, c8, c9)) =
      mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1+c1, b2+c2, b3+c3, b4+c4, b5+c5, b6+c6, b7+c7, b8+c8, b9+c9)"
    by simp
  also have "... = (a1*(b1+c1)+a2*(b4+c4)+a3*(b7+c7), a1*(b2+c2)+a2*(b5+c5)+a3*(b8+c8), a1*(b3+c3)+a2*(b6+c6)+a3*(b9+c9),
                    a4*(b1+c1)+a5*(b4+c4)+a6*(b7+c7), a4*(b2+c2)+a5*(b5+c5)+a6*(b8+c8), a4*(b3+c3)+a5*(b6+c6)+a6*(b9+c9),
                    a7*(b1+c1)+a8*(b4+c4)+a9*(b7+c7), a7*(b2+c2)+a8*(b5+c5)+a9*(b8+c8), a7*(b3+c3)+a8*(b6+c6)+a9*(b9+c9))"
    by simp
  also have "... = (a1*b1+a1*c1+a2*b4+a2*c4+a3*b7+a3*c7, a1*b2+a1*c2+a2*b5+a2*c5+a3*b8+a3*c8, a1*b3+a1*c3+a2*b6+a2*c6+a3*b9+a3*c9,
                    a4*b1+a4*c1+a5*b4+a5*c4+a6*b7+a6*c7, a4*b2+a4*c2+a5*b5+a5*c5+a6*b8+a6*c8, a4*b3+a4*c3+a5*b6+a5*c6+a6*b9+a6*c9,
                    a7*b1+a7*c1+a8*b4+a8*c4+a9*b7+a9*c7, a7*b2+a7*c2+a8*b5+a8*c5+a9*b8+a9*c8, a7*b3+a7*c3+a8*b6+a8*c6+a9*b9+a9*c9)"
    by (simp add: add_mult_distrib2)
  also have "... = mat3_add (a1*b1+a2*b4+a3*b7, a1*b2+a2*b5+a3*b8, a1*b3+a2*b6+a3*b9,
                             a4*b1+a5*b4+a6*b7, a4*b2+a5*b5+a6*b8, a4*b3+a5*b6+a6*b9,
                             a7*b1+a8*b4+a9*b7, a7*b2+a8*b5+a9*b8, a7*b3+a8*b6+a9*b9)
                  (a1*c1+a2*c4+a3*c7, a1*c2+a2*c5+a3*c8, a1*c3+a2*c6+a3*c9,
                   a4*c1+a5*c4+a6*c7, a4*c2+a5*c5+a6*c8, a4*c3+a5*c6+a6*c9,
                   a7*c1+a8*c4+a9*c7, a7*c2+a8*c5+a9*c8, a7*c3+a8*c6+a9*c9)"
    by simp
  also have "... = mat3_add (mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) (b1, b2, b3, b4, b5, b6, b7, b8, b9)) 
          (mat3_mul (a1, a2, a3, a4, a5, a6, a7, a8, a9) (c1, c2, c3, c4, c5, c6, c7, c8, c9))"
    by simp
  finally show ?thesis
    by simp
qed

end