
(*<*)
theory Vezbe11_resenja
    imports Main "HOL-Library.Multiset"
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Tip: 'a drvo]\<close>

text \<open>Definisati algebarski tip \<open>'a drvo\<close> koji predstavlja binarno drvo.\<close>

datatype 'a drvo = List
                 | Cvor "'a drvo" 'a "'a drvo"

text \<open>Definisati funkciju \<open>zbir :: nat drvo \<Rightarrow> nat\<close> primitivnom rekurzijom koja 
      računa zbir elemenata drveta tipa \<open>nat drvo\<close>. Da li je moguće definisati ovu
      funkciju nad tipom \<open>'a drvo\<close>?\<close>

primrec zbir :: "nat drvo \<Rightarrow> nat" where
  "zbir List = 0"
| "zbir (Cvor lt x rt) = zbir lt + x + zbir rt"

text \<open>Definisati bilo koju instancu \<open>test_drvo\<close> tipa \<open>nat drvo\<close>. Proveriti
      da li funkcija \<open>zbir\<close> daje dobar rezultat kada se primeni na \<open>test_drvo\<close>.\<close>

definition test_drvo :: "nat drvo" where
  "test_drvo \<equiv> Cvor (Cvor List 1 List) 3 (Cvor (Cvor List 4 List) 2 (Cvor List 3 List))"

value "zbir test_drvo"

text \<open>Definisati funkciju \<open>sadrzi :: 'a drvo \<Rightarrow> 'a \<Rightarrow> bool\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad 
      instancom \<open>test_drvo\<close>.\<close>

primrec sadrzi :: "'a drvo \<Rightarrow> 'a \<Rightarrow> bool" where
  "sadrzi List a \<longleftrightarrow> False"
| "sadrzi (Cvor ld x dd) a \<longleftrightarrow> sadrzi ld a \<or> x = a \<or> sadrzi dd a"

value "sadrzi test_drvo 3"
value "sadrzi test_drvo 5"

text \<open>Definisati funkciju \<open>skup :: 'a drvo \<Rightarrow> 'a set\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad
      instancom \<open>test_drvo\<close>.\\
      Pronaći vezu između funkcija \<open>skup\<close> i \<open>sadrzi\<close>. Formulisati i dokazati tu lemu.\<close>

primrec skup :: "'a drvo \<Rightarrow> 'a set" where
  "skup List = {}"
| "skup (Cvor ld x dd) = skup ld \<union> {x} \<union> skup dd"

value "skup test_drvo"

lemma pripada_skup_sadrzi:
  shows "a \<in> skup d \<longleftrightarrow> sadrzi d a"
  by (induction d) auto

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Obilazak stabla]\<close>

text \<open>Definisati funkciju \<open>infiks\<close> koja vraća listu čvorova stabla u infiksnom poretku.\<close>

primrec infiks :: "'a drvo \<Rightarrow> 'a list" where
  "infiks List = []"
| "infiks (Cvor ld x dd) = (infiks ld) @ [x] @ (infiks dd)"

text \<open>Pokazati korektnost ove funkcije. Dve invarijante:\<close>
text_raw 
\<open>\begin{enumerate} 
  \item Skup elemenata infiksnog obilaska drveta i skup elemenata drveta ostaju isti.
  \item Multiskup elemanata infiksnog obilaska drveta i skupa elemenata drveta ostaju isti.
\end{enumerate}\<close>
text \<open>\<open>Savet\<close>: Tip multiskupa: \<open>'a multiset\<close>,
               prazan multiskup se definiše kao \<open>{#}\<close>, 
               multiskup sa jednim elementom \<open>{#x#}\<close>,
               unija multiskupova je operator \<open>+\<close>.\<close>

lemma set_infiks_skup[simp]:
  shows "set (infiks d) = skup d"
  by (induction d) auto

primrec multiskup :: "'a drvo \<Rightarrow> 'a multiset" where
  "multiskup List = {#}"
| "multiskup (Cvor ld x dd) = multiskup ld + {#x#} + multiskup dd"

lemma mset_indiks_multiskup [simp]:
  shows "mset (infiks d) = multiskup d"
  by (induction d) auto

text \<open>Definisati efikasnu implementaciju infiksnog obilaska drveta \<open>infiks_opt\<close> i 
      pokazati da je ekvivalentna funkciju \<open>infiks\<close>.\<close>

primrec infiks_opt' :: "'a drvo \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "infiks_opt' List xs = xs"
| "infiks_opt' (Cvor ld x dd) xs = infiks_opt' ld (x # infiks_opt' dd xs)"

definition infiks_opt :: "'a drvo \<Rightarrow> 'a list" where
  "infiks_opt xs = infiks_opt' xs []"

value "infiks_opt test_drvo"

lemma infiks_opt'_append:
  shows "infiks_opt' d xs @ ys = infiks_opt' d (xs @ ys)"
  by (induction d arbitrary: xs) auto

lemma infiks_infiks_opt:
  shows "infiks d = infiks_opt d"
  unfolding infiks_opt_def
  by (induction d) (auto simp add: infiks_opt'_append)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Binarno pretraživačko stablo.]\<close>

text \<open>Definisati predikat \<open>sortirano\<close> nad binarnim stablom tipa \<open>('a::linorder) drvo\<close>
      koji ukazuje na to da li je stablo pretraživačko ili nije.
      Definisati instancu \<open>test_drvo_sortirano\<close> nad tipom \<open>nat drvo\<close> koja
      predstavlja binarno pretraživačko stablo. Testirati funkciju \<open>sortirano\<close>
      nad instancom \<open>test_drvo\<close> i \<open>test_drvo_sortirano\<close>.
      Zapisati i dokazati vezu između funkcije \<open>sortirano\<close> i \<open>infiks\<close>.\<close>

primrec sortirano :: "('a::linorder) drvo \<Rightarrow> bool" where
  "sortirano List \<longleftrightarrow> True"
| "sortirano (Cvor ld x dd) \<longleftrightarrow> (\<forall> a \<in> skup ld. a \<le> x) 
                              \<and> (\<forall> a \<in> skup dd. x \<le> a)
                              \<and> sortirano ld 
                              \<and> sortirano dd"

value "infiks test_drvo"
value "sortirano test_drvo"

definition test_drvo_sortirano :: "nat drvo" where
  "test_drvo_sortirano = Cvor (Cvor List 1 (Cvor List 2 List)) 3 (Cvor (Cvor List 3 List) 4 List)"

value "infiks test_drvo_sortirano"
value "sortirano test_drvo_sortirano"

lemma sortirano_sorted_infiks:
  shows "sortirano d \<Longrightarrow> sorted (infiks d)"
  by (induction d) (auto simp add: sorted_append order_trans)

text \<open>Primitivnom rekurzijom definisati funkciju \<open>ubaci :: 'a::linorder \<Rightarrow> 'a drvo \<Rightarrow> 'a drvo\<close>
      koja ubaciju element u binarno pretraživačko drvo.\<close>
text \<open>Pokazati da važe invarijante:\<close>
text_raw 
\<open>\begin{enumerate}
  \item Element će se nalaziti u drvetu nakon što se ubaci.
  \item Skup elemenata drveta nakon ubacivanja elementa se proširuje za taj element.
  \item Multiskup elemenata drveta nakon ubacivanja elementa se proširuje za taj element.
  \item Zbir elemenata drveta nakon ubacivanja elementa se povećava za njegovu vrednost.
  \item Nakon ubacivanja elementa u pretraživačko drvo, drvo ostaje pretraživačko.
\end{enumerate}\<close>

primrec ubaci :: "'a::linorder \<Rightarrow> 'a drvo \<Rightarrow> 'a drvo" where
  "ubaci a List = (Cvor List a List)"
| "ubaci a (Cvor ld x dd) = 
    (if a \<le> x then Cvor (ubaci a ld) x dd 
     else Cvor ld x (ubaci a dd))"

lemma sadrzi_ubaci [simp]:
  shows "sadrzi (ubaci x d) x"
  by (induction d) auto

lemma skup_ubaci [simp]:
  shows "skup (ubaci x d) = {x} \<union> skup d"
  by (induction d) auto

lemma multiskup_ubaci[simp]:
  shows "multiskup (ubaci x d) = {#x#} + multiskup d"
  by (induction d) auto

lemma zbir_ubaci [simp]:
  shows "zbir (ubaci x d) = x + zbir d"
  by (induction d) auto

lemma sortirano_ubaci [simp]:
  shows "sortirano d \<Longrightarrow> sortirano (ubaci x d)"
  by (induction d) auto

text \<open>Definisati funkciju \<open>listaUDrvo :: ('a::linorder) list \<Rightarrow> 'a drvo\<close> 
      koja od liste elemenata gradi binarno pretraživačko drvo.\<close>

primrec listaUDrvo :: "('a::linorder) list \<Rightarrow> 'a drvo" where
  "listaUDrvo [] = List"
| "listaUDrvo (x # xs) = ubaci x (listaUDrvo xs)"

text \<open>Pokazazati sledeće osobine funkcije \<open>listaUDrvo\<close>:\<close>
text_raw 
\<open>\begin{enumerate}
  \item listaUDrvo održava skup elemenata.
  \item listaUDrvo održava multiskup elemenata.
  \item listaUDrvo gradi binarno pretraživačko drvo.
\end{enumerate}\<close>

lemma [simp]: "skup (listaUDrvo xs) = set xs"
  by (induction xs) auto

lemma [simp]: "multiskup (listaUDrvo xs) = mset xs"
  by (induction xs) auto

lemma [simp]: "sortirano (listaUDrvo xs)"
  by (induction xs) auto

text \<open>Definisati funkciju koja sortira elemente liste pomoću stabla:\<close>

definition sortiraj :: "nat list \<Rightarrow> nat list" where
  "sortiraj xs = infiks (listaUDrvo xs)"

text \<open>Pokazati korektnost ove funkcije\<close>
text_raw
\<open>\begin{enumerate}
  \item Nakon primene funkcije lista je sortirana.
  \item Skup elemenata sortirane liste i početne liste ostaje isit.
  \item Multiskup elemenata sortirane liste i početne liste ostaje isti.
\end{enumerate}\<close>

theorem "sorted (sortiraj xs)"
  unfolding sortiraj_def
  by (induction xs) (auto simp add: sortirano_sorted_infiks)

theorem "set (sortiraj xs) = set xs"
  unfolding sortiraj_def
  by auto

theorem "mset (sortiraj xs) = mset xs"
  unfolding sortiraj_def
  by auto

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
