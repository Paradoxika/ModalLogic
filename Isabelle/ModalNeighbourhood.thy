(*<*) 
theory NModal
imports Main 

begin
(*>*)

section {* Introduction *}

section {* An Embedding of Neighbourhood-Based Modal Logics in HOL *}

text {* The types @{text "i"} for possible worlds and $\mu$ for individuals are introduced. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      

text {* Possible worlds are related by an accessibility relation @{text "r"} or by a neighbourhood function @{text "n"}.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

  consts n :: "i \<Rightarrow> ((i \<Rightarrow> bool) \<Rightarrow> bool)"    -- "neighbourhood function n"

text {* QML formulas are translated as HOL terms of type @{typ "i \<Rightarrow> bool"}. 
This type is abbreviated as @{text "\<sigma>"}. *}

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. The lifted connectives are @{text "m\<not>"}, @{text "m\<and>"}, @{text "m\<rightarrow>"},
@{text "\<forall>"}, and @{text "\<exists>"} (the latter two are modeled as constant symbols). 
Other connectives can be introduced analogously. We exemplarily do this for @{text "m\<or>"} , 
@{text "m\<equiv>"}, and @{text "mL="} (Leibniz equality on individuals). Moreover, the modal 
operators @{text "\<box>"} and @{text "\<diamond>"}  are introduced. Definitions could be used instead of 
abbreviations. *}

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"

  abbreviation subseteq :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix "subseteq" 53) where "p subseteq q \<equiv> \<forall>w. ((p w) \<longrightarrow> (q w))" 

  abbreviation inn :: "\<sigma> \<Rightarrow> (\<sigma> \<Rightarrow> bool) \<Rightarrow> bool" (infix "in" 52) where "p in N \<equiv> (N p)" 

  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<phi> in (n w))"

  abbreviation mfalse :: "\<sigma>" ("m\<bottom>") where "m\<bottom> \<equiv> \<lambda>w. False "
  abbreviation mtrue :: "\<sigma>" ("m\<top>") where "m\<top> \<equiv> \<lambda>w. True "

 (* abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)"  *)
  
text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  
section {* A Simple Deontic Logic *}  
  
text {* Semantic conditions *}
 
  axiomatization where
    upclosed: "\<forall>w.\<forall>p q. (p in (n w)) \<longrightarrow> (p subseteq q) \<longrightarrow> (q in (n w)) " and
    empty_not_in_neighbourhood: "\<forall>w. \<not> (m\<bottom> in (n w)) " and
    full_in_neighbourhood:  "\<forall>w. (m\<top> in (n w))"


text {* Automated proofs showing that the Hilbert style rules follow from the semantic conditions  *} 

  theorem necessitation: "\<forall>p. [p] \<longrightarrow> [\<box>p]"  
  sledgehammer [provers = remote_leo2] 
  by (metis (lifting) full_in_neighbourhood upclosed)

  theorem neg_necessitation: "\<forall>p. [m\<not> p] \<longrightarrow> [m\<not> (\<box> p)]"
  sledgehammer [provers = remote_leo2] 
  by (metis (lifting) empty_not_in_neighbourhood upclosed)

  theorem boxing_implication: "\<forall>p.\<forall>q. [p m\<rightarrow> q] \<longrightarrow> [(\<box> p) m\<rightarrow> (\<box> q)]"
  sledgehammer [provers = remote_leo2] 
  by (metis (lifting) upclosed) 


text {* A simple example theorem in this deontic logic, proved automatically  *} 

  theorem example1: "\<forall>p. \<forall>q. [\<box>(p m\<and> q) m\<rightarrow> (\<box>p m\<and> \<box>q) ]" 
  sledgehammer [provers = remote_leo2]
  by (metis (lifting, no_types) boxing_implication)  


text {* Counter-satisfiable examples, with countermodels found by Nitpick *} 

  theorem nontheorem1: "\<forall>p. [\<box>p m\<rightarrow> p ]"
  nitpick [user_axioms = true] oops

  theorem nontheorem2: "\<forall>p. \<forall>q. [\<box>(p m\<or> q) m\<rightarrow> (\<box>p m\<or> \<box>q) ]" 
  nitpick [user_axioms = true] oops

(*<*) 
end
(*>*) 