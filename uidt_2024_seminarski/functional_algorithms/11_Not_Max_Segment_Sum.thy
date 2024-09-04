theory "11_Not_Max_Segment_Sum"
	imports Main
begin

(*Author: Mihailo Simic 267/2018*)


(*Funkcija koja pravi kombinacije ne-segmenata*)
(*Pravi ne segmente specifirajuci da li se element nalazi (True) ili ne nalazi u ne-segmentu (False)*)
fun booleans :: "nat \<Rightarrow> bool list list" where
  "booleans 0 = [[]]" |
  "booleans (Suc n) = concat (map (\<lambda>bs. [True # bs, False # bs]) (booleans n))"

(*Funkcija koja pakuje dve liste u jednu po parovima*)
fun zip :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "zip [] [] = []" |
  "zip (x#xs) (y#ys) = (x, y) # zip xs ys" |
  "zip _ _ = []"

(*Kreira listu torki uparujuci svaki element liste sa svakim ne-segmentom (booleans)*)
fun markings :: "'a list \<Rightarrow> ('a \<times> bool) list list" where
  "markings xs = map (\<lambda>bs. zip xs bs) (booleans (length xs))"

(*Funkcija koja proverava da li joj je prosledjen non-segment*)
(*Ulaz je lista parova koji predstavlja marking, ako taj marking predstavlja ne-segment vraca True, False inace*)
fun nonseg :: "('a \<times> bool) list \<Rightarrow> bool" where
  "nonseg [] = False" |
  "nonseg [(x, True)] = False" |  (* Jedno True ne moze biti ne-segment *)
  "nonseg [(x, False)] = False" | (* Slicno ni jedno False ne moze biti ne-segment *)
  "nonseg ((x1, False) # (x2, True) # (x3, False) # rest) = True" | (* Poklapamo sablon False True False*)
  "nonseg ((x1, False) # rest) = nonseg rest" | (* Preskacemo prvo False*)
  "nonseg ((x1, True) # rest) = False"  (* Ako je prvo True bez prethodnih False *)

(*Funkcija koja ekstraktuje ne-segmente*)
(*Vraca listu elemenata iz originalne liste koja ima vrednost True*)
fun extract2 :: "('a \<times> bool) list list \<Rightarrow> 'a list list" where
  "extract2 xss = map (map fst \<circ> filter snd) xss"

(*Funkcija koja vraca sve ne-segmente za datu listu brojeva*)
fun nonsegs :: "'a list \<Rightarrow> 'a list list" where
  "nonsegs xs = extract2 (filter nonseg (markings xs))"

(*Denifisali smo nasu funkciju za sumiranje niza prirodnih brojeva*)
fun sum_list :: "int list \<Rightarrow> int" where
  "sum_list [] = 0" | 
  "sum_list (x#xs) = x + sum_list xs"

(*Funkcija za trazenje maksimuma niza*)
(*Trazi maksimum celog niza preko binarne funkcije max a b*)
fun maximum :: "int list \<Rightarrow> int" where
  "maximum [] = 0"  |
  "maximum [x] = x" |
  "maximum (x#xs) = max x (maximum xs)"

(*Konacna funkcija za racunanje maksimalne sume ne-segmenta*)
fun mnss :: "int list \<Rightarrow> int" where
  "mnss xs = (if xs = [] then 0 else maximum (map sum_list (nonsegs xs)))"


(*Formulacija lema za funkcije*)

lemma nonseg_correctness:
  assumes "nonseg xms"
  shows "\<exists>i j k. (i < j \<and> j < k) \<and> (snd (xms ! i) = False) \<and> (snd (xms ! j) = True) \<and> (snd (xms ! k) = False)"
  using assms
proof (induction xms rule: nonseg.induct)
  case 1
  then show ?case by auto
next
  case (2 x)
  then show ?case by auto
next
  case (3 x)
  then show ?case by auto
next
  case (4 x1 x2 x3 rest)
  then show ?case
  proof-
    let "?i" = 0
    let "?j" = 1
    let "?k" = 2
    have "snd (xms ! ?i) = False" by (cases xms, auto)
    moreover have "snd (xms ! ?j) = True" by (cases xms, auto)
    moreover have "snd (xms ! ?k) = False" by (cases xms, auto)
    moreover have " \<exists>i j k. i < j \<and> j < k" by auto
    ultimately show ?thesis by auto
  qed
next
  case ("5_1" x1 vb va)
  then obtain i j k where "i < j \<and> j < k" and "snd (va ! i) = False" and "snd (va ! j) = True" and "snd (va ! k) = False"
    using "5_1" by auto
  then show ?case
  proof -
    (* Sablon F T F je u ostatku liste, pomeramo se za 1 udesno *)
    have "i+1 < j+1 \<and> j+1 < k+1" using `i < j \<and> j < k` by auto
    thus ?thesis
      by (smt (verit, ccfv_SIG) Suc_less_eq \<open>i < j \<and> j < k\<close> \<open>snd (va ! i) = False\<close> \<open>snd (va ! j) = True\<close> \<open>snd (va ! k) = False\<close> nth_Cons_Suc)
  qed
next
  case ("5_2" x1 v)
  then show ?case sorry
next
  case ("5_3" x1 v vd rest)
  then obtain i j k where "i < j \<and> j < k" and "snd (rest ! i) = False" and "snd (rest ! j) = True" and "snd (rest ! k) = False"
    using "5_3" by auto
  then show ?case
  proof -
    (* Sablon se nalazi negde dalje u listi (slicno kao i kod 5_1) *)
    have "i+1 < j+1 \<and> j+1 < k+1" using `i < j \<and> j < k` by auto
    thus ?thesis
      using "5_3.IH" "5_3.prems" Suc_mono nonseg.simps(7) nth_Cons_Suc by fastforce
  qed
next
  case (6 x1 v va)
  then show ?case
    by (smt (verit, del_insts) Suc_mono nonseg.simps(8) nth_Cons_Suc)
qed


lemma nonsegs_correctness:
  assumes "ys \<in> set (nonsegs xs)"
  shows "\<exists>ms. ms \<in> set (markings xs) \<and> ys = map fst (filter snd ms) \<and> nonseg ms"
  using assms by auto



lemma mnss_correctness:
  assumes "xs \<noteq> []"
  shows "mnss xs = Max (set (map sum_list (nonsegs xs)))"
  sorry

(* Test primeri *)
value "booleans 3"
value "markings [1::int,2,3]"
value "set(markings [1::int,2,3])"
value "nonsegs [1::int, 2, 3, 4, 5]"
value "maximum [1::int,2,3]"
value "mnss [-4, -3, -7, 2, 1, -2, -1, -4]"


end
