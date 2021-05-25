theory mi17039_Vladimir_Arsenijevic
  imports Main
begin

text‹
  https://www.imo-official.org/problems/IMO2018SL.pdf

  3.zadatak
  Antipaskalov trougaoje tablica u obliku jednakostraniqnog trouglakoja se sastoji od brojeva tako da, osim za brojeve u poslednjem redu, vazi da je svakibroj jednak apsolutnoj vrednosti razlike dva broja koja su neposredno ispod njega. Da li postoji antipaskalov trougao sa 2018 redova koji se sastoji od svih prirodnihbrojeva od 1 do 1 + 2 +···+ 2018?
›

(*
   1
  3 2
 2 5 3
2 4 9 6

1 | 3 2 | 2 5 3 | 2 4 9 6
2 4 9 6 2 5 3 3 2 1
*)

fun vrednost :: "int list\<Rightarrow>int list" where
"vrednost [] = []" |
"vrednost [x] = [x]" |
"vrednost [x,y] = [abs(x-y)]" |
"vrednost (x#y#xs) = vrednost (y#xs) @ [abs(x-y)]"

lemma len_vrednost_manje_len_x:
  shows "length (vrednost x) \<le> length x"
  apply(induction x)
   apply fastforce
  sorry

fun vrednost' :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vrednost' x [] = []" |
"vrednost' x [y] = [y]" |
"vrednost' x y = x@(vrednost' (vrednost y) (vrednost y))"

value "length []"
value "vrednost [2::int,4,9,6]"
value "vrednost [3::int,5,2]"
value "vrednost [3::int,2]"
value "vrednost' [] [2::int,4,9,6]"

fun antiPaskal :: "int list \<Rightarrow> int list" where
"antiPaskal x = vrednost' [] x"

end
