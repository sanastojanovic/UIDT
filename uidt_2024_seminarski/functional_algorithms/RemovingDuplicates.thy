theory RemovingDuplicates
  imports Main

(*Milica Kuzet 64/2020*)

begin

(*funkcija koja izbacuje duplikate*)
fun nub:: "'a list \<Rightarrow> 'a list" where
"nub [] = []" |
"nub (x#xs) = x # nub (filter (\<lambda>y. y\<noteq>x) xs)"

value "nub [1::int, 2, 5, 3, 5, 7, 2, 1]" (*ocekivan izlaz: [1, 2, 5, 3, 7]*)

(*funkcija koja leksikografski poredi dve liste*)
fun lex_min :: "'a::ord list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"lex_min [] ys = []" |
"lex_min xs [] = xs" | 
"lex_min (x#xs) (y#ys) = 
      (if x<y then (x#xs)
      else if x>y then (y#ys)
      else lex_min xs ys)"

value "lex_min [1::int,3,4,7,2] [8::int,7,9]" (*ocekivan izlaz: [1,3,4,7,2]*)

(*funkcija koja uklanja samo prvo pojavljivanje elementa x iz liste*)
fun remove_first :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove_first x [] = []" |
"remove_first x (y#ys) = (if x=y then ys else y # remove_first x ys)"

value "remove_first 1 [2::int,3,4,5,1,4,1]" (*ocekivan izlaz: [2, 3, 4, 5, 4, 1]*)

(*operacija remove_first smanjuje duzinu liste*)
lemma remove_first_decreases_length:
  assumes "x \<in> set xs"
  shows "length (remove_first x xs) < Suc (length xs)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case
  proof (cases "x = y")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using Cons by simp
  qed
qed

(*funkcija koja vraca sortiranu listu bez duplikata*)
function nub_min :: "'a::linorder list \<Rightarrow> 'a list" where
"nub_min [] = []" |
"nub_min (x#xs) = 
   (if x \<notin> set xs then x # nub_min xs 
    else lex_min (x # nub_min (remove_first x xs)) (nub_min xs))"
  by pat_completeness auto
termination
  apply (relation "measure length") 
  apply (auto simp add: remove_first_decreases_length)
  done

value "nub_min [3::int, 1, 2, 3, 2]"   (*ocekivan izlaz: [1, 2, 3]*)

(*generalizacija: funkcija koja vraca sortiranu listu bez duplikata*)
fun hub :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "hub ws [] = []" |
  "hub ws (x # xs) =
    (if x \<in> set ws then
      if x \<in> set xs then hub ws xs
      else let us = takeWhile (\<lambda>y. y < x) ws;
               vs = dropWhile (\<lambda>y. y < x) ws;
               removed = removeAll x xs;
               sorted_vs = sort (tl vs);
               sorted_removed = sort removed
           in lex_min (sort (us @ [x] @ hub sorted_vs sorted_removed)) 
                      (sort (us @ [x] @ hub [] sorted_removed))
    else let us = takeWhile (\<lambda>y. y < x) ws;
             sorted_removed = sort (removeAll x xs)
         in sort (us @ [x] @ hub [] sorted_removed))"

value "hub [] [3::int, 1, 2, 3, 2]"  (*ocekivan izlaz: [1, 2, 3]*)

(*SKUPOVI*)

(*standardne funkcije za rad sa skupovima*)
fun insert_set :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"insert_set x s = insert x s"

fun split_set :: "'a::ord \<Rightarrow> 'a set \<Rightarrow> ('a set * 'a set)" where
"split_set x s = ({y \<in> s. y < x}, {y \<in> s. y > x})"

fun elems_set :: "'a::linorder set \<Rightarrow> 'a list" where
"elems_set s = sorted_list_of_set s"

(*funkcija koja uz svaki element pridruži skup elemenata koji dolaze nakon njega u originalnoj listi.  *)
fun preprocess :: "'a::linorder list \<Rightarrow> ('a * 'a set) list" where
"preprocess [] = []" |
"preprocess (x#xs) = 
  (x, foldr Set.insert xs {}) # preprocess xs"

(*funkcija koja koristeci skupove vraca sortiranu listu bez duplikata*)
fun hub' :: "'a::linorder set \<Rightarrow> 'a::linorder set \<Rightarrow> ('a * 'a set) list \<Rightarrow> 'a list" where
"hub' ps ws [] = []" |
"hub' ps ws ((x, xs_set)#xss) =
  (if x \<in> ps then hub' ps ws xss
   else let (us, vs) = split_set x ws;
            eus = elems_set us;
            yss = filter (\<lambda>(x, xs_set). x \<notin> (ps \<union> us)) xss
        in eus @ [x] @ hub' (insert_set x ps) vs yss)"

(*glavna funkcija *)
fun hubSet :: "'a::linorder list \<Rightarrow> 'a list" where
"hubSet xs = hub' {} (set xs) (preprocess xs)"

value "hubSet [3::int, 1, 2, 3, 2]"  (*ocekivan izlaz: [1, 2, 3]*)
value "hubSet [3::int, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]"  (*ocekivan izlaz: [1, 2, 3, 4, 5, 6, 9]*)

(*funkcija koja koristeci skupove vraca sortiranu listu bez duplikata *)
(*efikasnije jer izbegava ponovnu proveru elemenata iz eus*)
fun hub'' :: "'a::linorder set \<Rightarrow> 'a::linorder set \<Rightarrow> ('a * 'a set) list \<Rightarrow> 'a list" where
"hub'' ps ws [] = []" |
"hub'' ps ws ((x, xs_set)#xss) =
  (if x \<in> ps then hub'' ps ws xss
   else let (us, vs) = split_set x ws;
            eus = elems_set us;
            qs = foldr insert_set eus (insert_set x ps); 
            yss = filter (\<lambda>(x', xs_set'). x' \<notin> qs) xss
        in eus @ [x] @ hub' qs vs yss)"

(*glavna funkcija *)
fun hubSetFinal :: "'a::linorder list \<Rightarrow> 'a list" where
"hubSetFinal xs = hub'' {} (set xs) (preprocess xs)"

value "hubSetFinal [3::int, 1, 2, 3, 2]" (*ocekivan izlaz: [1, 2, 3]*)
value "hubSetFinal [3::int, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]" (*ocekivan izlaz: [1, 2, 3, 4, 5, 6, 9]*)


end