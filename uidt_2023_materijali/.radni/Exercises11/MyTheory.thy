
(*<*)
theory MyTheory
    imports Main "HOL-Library.Multiset"
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Tip: 'a drvo]\<close>

text \<open>Definisati algebarski tip \<open>'a drvo\<close> koji predstavlja binarno drvo.\<close>

datatype 'a drvo = undef

text \<open>Definisati funkciju \<open>zbir :: nat drvo \<Rightarrow> nat\<close> primitivnom rekurzijom koja 
      računa zbir elemenata drveta tipa \<open>nat drvo\<close>. Da li je moguće definisati ovu
      funkciju nad tipom \<open>'a drvo\<close>?\<close>

text \<open>Definisati bilo koju instancu \<open>test_drvo\<close> tipa \<open>nat drvo\<close>. Proveriti
      da li funkcija \<open>zbir\<close> daje dobar rezultat kada se primeni na \<open>test_drvo\<close>.\<close>

text \<open>Definisati funkciju \<open>sadrzi :: 'a drvo \<Rightarrow> 'a \<Rightarrow> bool\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad 
      instancom \<open>test_drvo\<close>.\<close>

text \<open>Definisati funkciju \<open>skup :: 'a drvo \<Rightarrow> 'a set\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad
      instancom \<open>test_drvo\<close>.\\
      Pronaći vezu između funkcija \<open>skup\<close> i \<open>sadrzi\<close>. Formulisati i dokazati tu lemu.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Obilazak stabla]\<close>

text \<open>Definisati funkciju \<open>infiks\<close> koja vraća listu čvorova stabla u infiksnom poretku.\<close>

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

text \<open>Definisati efikasnu implementaciju infiksnog obilaska drveta \<open>infiks_opt\<close> i 
      pokazati da je ekvivalentna funkciju \<open>infiks\<close>.\<close>

definition infiks_opt :: "'a drvo \<Rightarrow> 'a list" where
  "infiks_opt xs = undefined"

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Binarno pretraživačko stablo.]\<close>

text \<open>Definisati predikat \<open>sortirano\<close> nad binarnim stablom tipa \<open>('a::linorder) drvo\<close>
      koji ukazuje na to da li je stablo pretraživačko ili nije.
      Definisati instancu \<open>test_drvo_sortirano\<close> nad tipom \<open>nat drvo\<close> koja
      predstavlja binarno pretraživačko stablo. Testirati funkciju \<open>sortirano\<close>
      nad instancom \<open>test_drvo\<close> i \<open>test_drvo_sortirano\<close>.
      Zapisati i dokazati vezu između funkcije \<open>sortirano\<close> i \<open>infiks\<close>.\<close>

definition test_drvo_sortirano :: "nat drvo" where
  "test_drvo_sortirano = undefined"

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

text \<open>Definisati funkciju \<open>listaUDrvo :: ('a::linorder) list \<Rightarrow> 'a drvo\<close> 
      koja od liste elemenata gradi binarno pretraživačko drvo.\<close>

text \<open>Pokazazati sledeće osobine funkcije \<open>listaUDrvo\<close>:\<close>
text_raw 
\<open>\begin{enumerate}
  \item listaUDrvo održava skup elemenata.
  \item listaUDrvo održava multiskup elemenata.
  \item listaUDrvo gradi binarno pretraživačko drvo.
\end{enumerate}\<close>

text \<open>Definisati funkciju koja sortira elemente liste pomoću stabla:\<close>

definition sortiraj :: "nat list \<Rightarrow> nat list" where
  "sortiraj xs = undefined"

text \<open>Pokazati korektnost ove funkcije\<close>
text_raw
\<open>\begin{enumerate}
  \item Nakon primene funkcije lista je sortirana.
  \item Skup elemenata sortirane liste i početne liste ostaje isit.
  \item Multiskup elemenata sortirane liste i početne liste ostaje isti.
\end{enumerate}\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
