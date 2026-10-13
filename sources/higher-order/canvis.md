# Canvis a `main.tex`: resolució dels comentaris en roig

Data: 2026-10-13. Fitxer: `sources/higher-order/main.tex`.

Hi havia set comentaris en roig (`\textcolor{red}{…}`); un vuité, «Subseccions
extra», ja l'havies esborrat tu abans de començar. Tots set s'han resolt i
eliminat. Totes les etiquetes LaTeX existents es conserven (el pla de
`sources/higher-order/*.toml` hi fa referència) i se n'han afegit de noves.
El document compila sense errors ni referències indefinides (pdflatex + bibtex).

Al final hi ha la llista de **decisions que has de revisar**.

---

## 1. Derivors generalitzats (`SGenDerivors`)

**Comentari.** No volem sorts ordenats ni predicats; treballem amb
E-equacions, no amb fórmules. La $d_{\mathbf{w},s}$ de l'apartat 3 ha de
correspondre amb la $d$ de la Definició `DDerivor`. Les paraules es denoten
$\mathbf{s}$. Un derivor generalitzat és una tripla $(\varphi, D, d)$ amb
$(\varphi,d)$ un derivor i $D$ un conjunt d'E-equacions per a cada sort.

**Què he fet.**

- He afegit un paràgraf de notació, que també fan servir les seccions 5 i 6:
  - $v^{\mathbf{t}}_{j}$ és la variable de $\downarrow\mathbf{t}$ corresponent a la lletra $j$.
  - $\mathrm{Eq}_{\Lambda}(X)=\coprod_{t}\mathrm{T}_{\Lambda}(X)^2_t$ és el conjunt de les E-equacions.
  - $\mathbf{B}\models\mathcal{E}[b]$ indica satisfacció sota una valoració; una família $\mathbf{b}\in B_{\mathbf{t}}$ s'identifica amb una valoració.
  - $f^{\sharp}[\mathcal{E}]$ és la substitució aplicada a un conjunt d'equacions.
- He reescrit `DGeneralDerivor`:
  - Un derivor generalitzat és $(\varphi,D,d)$, on $(\varphi,d)$ és un derivor en el sentit de `DDerivor` i $D_s\subseteq\mathrm{Eq}_\Lambda(\downarrow(\varphi(s)))$ són E-equacions en l'única variable $v^{\varphi(s)}_0$.
  - Defineix també $D_{\mathbf{s}}$ per a paraules: les condicions de cada lletra, reanomenades a la variable corresponent.
- He explicat la correspondència amb [LG18]: $D_s$ correspon a $\Delta_s(x)$, i $d_{\mathbf{s},s}(\sigma)$ correspon a $\Phi^\sigma$. Tot derivor és el derivor generalitzat $(\varphi,\varnothing,d)$.
- He afegit la nova Observació `RGenDerivorSem`, sobre la semàntica pretesa:
  - L'àlgebra $\mathbf{B}$ es restringeix als subconjunts $B^D_s$.
  - Perquè això done una $\Sigma$-àlgebra cal una **condició de clausura**. No l'he posada a la definició, perquè el comentari no la demanava. Apareix en forma sintàctica a la secció 6, com a condició (GEP1).

## 2. ep-derivors (`SEpDerivors`)

**Comentari.** Denotar una ep-signatura per $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$.
Completar formalment $\mathrm{deft}^{\mathbf{\Sigma}}$ i l'operador de
conseqüència semàntica $\mathrm{Cn}$. Corregir la definició d'ep-derivor
tenint en compte el comentari que la seguia («I am not sure that this is the
correct definition…»).

**Què he fet** (la secció s'ha reescrit sencera):

- **`DEpSignature`** (nova): defineix l'ep-signatura $(S,\Sigma,\mathrm{def}^{\mathbf{\Sigma}})$ amb $\mathrm{def}^{\mathbf{\Sigma}}(\sigma)\subseteq\mathrm{Eq}_\Sigma(\downarrow\mathbf{s})$, el conjunt $A_{\mathrm{def}(\sigma)}$, les ep-àlgebres i la categoria $\mathsf{PAlg}(\mathbf{\Sigma})$. També corregeix les errades del text antic: $\mathbf{w}\to\mathbf{s}$ i «ordred». Una signatura total és el cas $\mathrm{def}=\varnothing$.
- **`RSubst`** (nova): lema de substitució per a àlgebres parcials. Només val quan els termes substituïts estan definits. Aquesta restricció és la causa de la correcció del punt 4 de més avall.
- **`DDeft`** (nova): $\mathrm{deft}^{\mathbf{\Sigma}}$ es defineix per recursió algebraica:
  $\mathrm{deft}(x)=\varnothing$ i
  $\mathrm{deft}(\sigma(P_j)_j)=\bigcup_j\mathrm{deft}(P_j)\cup(P_j)_j^{\sharp}[\mathrm{def}(\sigma)]$.
- **`LDeft`** (nou lema, amb prova): en una ep-àlgebra, $P^{\mathbf{A}}[a]$ està definit si i només si $\mathbf{A}\models\mathrm{deft}(P)[a]$. Aquesta és la justificació de $\mathrm{deft}$.
- **`DCn`** (nova): $\mathrm{Cn}^{\mathbf{\Sigma}}_X(\mathcal{E})$ és el conjunt de les E-equacions que valen en tota ep-àlgebra i sota tota valoració que satisfà $\mathcal{E}$. He afegit un paràgraf que diu que és un operador de clausura i que $\mathrm{Cn}(\mathcal{E})=\mathrm{Cn}(\mathcal{E}')$ si i només si $\mathcal{E}$ i $\mathcal{E}'$ tenen els mateixos models.
- **$\mathbf{d}^{\ast}(\mathbf{B})$**: la $\Sigma$-àlgebra parcial que s'obté interpretant cada $\sigma$ com l'operació terme parcial $d(\sigma)^{\mathbf{B}}$.
- **`DTranslation`** (nova) i **`LTranslation`** (nou lema, amb prova): la traducció $\mathrm{tr}_{\mathbf{d}}$ compleix que $\mathbf{d}^{\ast}(\mathbf{B})\models\mathcal{E}[\mathbf{b}]$ si i només si $\mathbf{B}\models\mathrm{tr}_{\mathbf{d}}[\mathcal{E}][\mathbf{b}]$. Vegeu el punt 4 de més avall.
- **`DDerivorEP`** (corregida). Abans era una còpia literal de `DDerivor`. Ara diu que un ep-derivor és un derivor tal que, per a cada $\sigma$,
  $$\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}^{\mathbf{\Lambda}}(\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))).$$
- **`PEpDerivorFunctor`** (nova, amb prova): $\mathbf{d}$ és un ep-derivor **si i només si** $\mathbf{d}^{\ast}$ envia $\mathbf{\Lambda}$-àlgebres a $\mathbf{\Sigma}$-àlgebres. En aquest cas $\mathbf{d}^{\ast}$ és un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`REpDerivor`** (nova): substitueix el paràgraf «I am not sure…» i explica les correccions.

**Les correccions a la definició antiga, i per què:**

1. **Inclusió → igualtat.** La inclusió
   $d^\sharp\times d^\sharp[\mathrm{def}(\sigma)]\subseteq\mathrm{Cn}(\mathrm{def}(d^\sharp(\sigma)))$
   només garanteix que el domini de $d(\sigma)^{\mathbf{B}}$ està contingut en el conjunt de les famílies que satisfan $\mathrm{def}(\sigma)$. L'operació podria quedar indefinida on hauria d'estar definida, i aleshores $\mathbf{d}^*(\mathbf{B})$ no seria una ep-àlgebra. La igualtat de conseqüències, que és la condició de Reichel, és **exactament** la que fa que $\mathbf{d}^*$ siga un functor; ho prova `PEpDerivorFunctor`. Això confirma la sospita del comentari.
2. **$\mathrm{def}(d^\sharp(\sigma))\to\mathrm{deft}^{\mathbf{\Lambda}}(d_{\mathbf{s},s}(\sigma))$.** $d(\sigma)$ és un terme, i cal $\mathrm{deft}$, no $\mathrm{def}$.
3. **$d^\sharp_{\mathbf{s},s}\to d^\sharp$ en totes les components.** Les equacions de $\mathrm{def}(\sigma)$ poden ser de qualsevol sort, no només de $s$.
4. **$d^\sharp\times d^\sharp\to\mathrm{tr}_{\mathbf{d}}$** (correcció nova, no demanada al comentari). Si $d(\sigma)$ no conté alguna variable, per exemple $d(\sigma)=v_0$ per a un $\sigma$ binari, aleshores $d^\sharp(\sigma(P_0,P_1))=d^\sharp(P_0)$ pot estar definit en $\mathbf{B}$ encara que $P_1$ no ho estiga en $\mathbf{d}^*(\mathbf{B})$. Per tant, $(d^\sharp P,d^\sharp Q)$ no expressa que $(P,Q)$ valga en $\mathbf{d}^*(\mathbf{B})$. $\mathrm{tr}_{\mathbf{d}}(P,Q)$ hi afegeix les equacions $(d^\sharp R,d^\sharp R)$ per a cada subterme $R$ de $P$ i de $Q$. Si cada $d(\sigma)$ conté totes les seues variables, aquestes equacions són redundants, i el text ho diu.

## 3. ep-derivors generalitzats (`SGenEpDerivors`)

**Comentari.** Completar una definició d'ep-derivor prenent com a base els
derivors generalitzats.

**Què he fet** (la secció era buida):

- **`DGenEpDerivor`** (nova): un ep-derivor generalitzat entre ep-signatures és un derivor generalitzat $(\varphi,D,d)$ tal que, per a cada $\sigma\in\Sigma_{\mathbf{s},s}$:
  - **(GEP1)**, preservació del domini:
    $d(\sigma)^{\sharp}[D_s]\subseteq\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$;
  - **(GEP2)**, condicions de domini dins dels dominis:
    $\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{tr}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])=\mathrm{Cn}(D_{\mathbf{s}}\cup\mathrm{deft}^{\mathbf{\Lambda}}(d(\sigma)))$.

  $\mathbf{d}^*(\mathbf{B})$ té com a conjunt subjacent els $B^D_s$, i les operacions són les restriccions de $d(\sigma)^{\mathbf{B}}$.
- **`PGenEpDerivorFunctor`** (nova, amb prova): un ep-derivor generalitzat indueix un functor $\mathsf{PAlg}(\mathbf{\Lambda})\to\mathsf{PAlg}(\mathbf{\Sigma})$.
- **`RGenEpDerivor`** (nova): comprova la coherència amb les seccions anteriors:
  - els ep-derivors són el cas $D=\varnothing$;
  - per a signatures totals, (GEP2) és trivial i (GEP1) equival a la condició de clausura de `RGenDerivorSem`;
  - les dues condicions també són necessàries.

## 4. $\Sigma^{(n)}$ com a ep-signatura (`DSigmaCatCompact`)

**Comentari.** Completar $\Sigma^{(n)}$ com una ep-signatura on l'únic domini
de definició no trivial és
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.

**Què he fet.**

- A `DSigmaCatCompact` he afegit l'ep-signatura $\mathbf{\Sigma}^{(n)}=(S,\Sigma^{(n)},\mathrm{def}^{\mathbf{\Sigma}^{(n)}})$:
  - les condicions de domini són buides per a les operacions de $\Sigma$, per a $\mathrm{sc}^k_s$ i per a $\mathrm{tg}^k_s$;
  - per a la composició, $\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))\}$, on $v^s_0\circ^k_s v^s_1$ abreuja $\circ^k_s(v^s_0,v^s_1)$.
- **Observació `RCompactEp`** (nova): les ep-àlgebres de tipus $\mathbf{\Sigma}^{(n)}$ són exactament les $\Sigma^{(n)}$-àlgebres parcials que compleixen (A0), (A$^k$1) i (A$^k$3). Per tant, la QE-varietat de `DVarCompact` és la classe de les $\mathbf{\Sigma}^{(n)}$-àlgebres que compleixen la resta d'axiomes.

⚠️ **He invertit l'ordre de les variables respecte del comentari** (vegeu la decisió A).

## 5. Categoria compacta $\omega$ abans de `DSigmaCatCompact`, i cas $\omega$

**Comentari.** Escriure la definició de categoria compacta $\omega$ abans de
`DSigmaCatCompact`, i modificar `DSigmaCatCompact` perquè considere també el
cas $\omega$.

**Què he fet.**

- He mogut `DCompactOmegaCat` i `DOmegaCatAlg` just després de `DManySortedCatAlg`, amb una frase introductòria. He mogut també l'àlgebra, i no només la categoria, perquè és el seu anàleg natural.
- A `DSigmaCatCompact` ara $n\in\mathbb{N}\cup\{\omega\}$. La nota posterior diu que $\Sigma^{(n)}\subseteq\Sigma^{(m)}$ per a $n\le m\le\omega$ i que $\Sigma^{(\omega)}=\bigcup_n\Sigma^{(n)}$.
- Dins de `RCompactEp` he afegit una nota: **`DVarCompact` no s'estén a $n=\omega$.** La condició «tota cel·la és una $k$-cel·la per a algun $k$» no es preserva per productes, i les QE-varietats sí que són tancades per productes. El text en dona un contraexemple.

## 6. Notació $\circ^{(j,k)}$ a la presentació estesa

**Comentari.** La $j$-composició de $k$-cel·les es denotarà $\circ^{(j,k)}$,
com ja fan `DSigmaCatExtended` i `DVarExtended`.

**Què he fet.** He substituït $\circ^{(j)}$ i $\circ^{(i)}$ a `DOmegaCatExt`, a
les $n$-categories esteses i als $n$-functors estesos. L'índex superior és
sempre la dimensió de les cel·les compostes:

- **(MS3):** $\mathrm{sc}^{(j,k)}(g\circ^{(i,k)}f)=\mathrm{sc}^{(j,k)}(g)\circ^{(i,j)}\mathrm{sc}^{(j,k)}(f)$.
- **(MS8):** $\mathrm{i}^{(k,j)}(g\circ^{(i,j)}f)=\mathrm{i}^{(k,j)}(g)\circ^{(i,k)}\mathrm{i}^{(k,j)}(f)$. He eliminat la frase aclaridora («on the left … on the right …»), perquè la notació ja ho diu.
- **(MS9), (MS2), (MS6), (MS7):** $\circ^{(i,k)}$ i $\circ^{(j,k)}$, segons el cas.
- **Functors:** $F_k(g\circ^{(j,k)}f)=F_k(g)\circ'^{(j,k)}F_k(f)$.
- **Dades:** $\zeta_{j,k}=(\circ^{(j,k)},\mathrm{sc}^{(j,k)},\mathrm{tg}^{(j,k)},\mathrm{i}^{(k,j)})$. A més, «$j$-composition in $C_k$» ara diu «$j$-composition of $k$-cells».

Al document ja no hi queda cap $\circ^{(j)}$ ni cap $\circ^{(i)}$.

## 7. Moure `DOmegaExtCatAlg` i cas $\omega$ de `DSigmaCatExtended`

**Comentari.** Moure aquesta definició abans de `DSigmaCatExtended` i
modificar `DSigmaCatExtended` perquè considere també el cas $\omega$.

**Què he fet.**

- He mogut `DOmegaExtCatAlg` just després de `DExtCatAlg`, és a dir, abans de `DSigmaCatExtended`.
- A `DSigmaCatExtended` ara $n\in\mathbb{N}\cup\{\omega\}$. He introduït la notació $[n]$ per al conjunt de dimensions: $[n]=n+1$ si $n\in\mathbb{N}$, i $[\omega]=\omega$. Cal perquè, per a $\omega$, els sorts són $\omega\times S$ i no $(\omega+1)\times S$. He canviat $n+1$ per $[n]$ dins de la definició.
- La nota posterior diu que $\Sigma^{\mathrm{ext}(\omega)}$ és la unió de les imatges de les inclusions de $\Sigma^{\mathrm{ext}(n)}$, i que per a $n$ finit $[n]=n+1$, que és la notació de les altres definicions.

---

## Decisions que has de revisar

**A. Ordre dels arguments de $\circ^k_s$ (punt 4).** El comentari escrivia
$\mathrm{def}(\circ^k_s)=\{(\mathrm{sc}^k_s(v^s_1),\mathrm{tg}^k_s(v^s_0))\}$.
Amb la convenció del document, $x\circ^k_s y=\circ^k_s(x,y)$, i (A$^k$3) diu
que $x\circ^k_s y$ està definit si i només si
$\mathrm{sc}^k_s(x)=\mathrm{tg}^k_s(y)$. Amb $x=v^s_0$ i $y=v^s_1$, això dona
$(\mathrm{sc}^k_s(v^s_0),\mathrm{tg}^k_s(v^s_1))$, que és el que he escrit. La
versió del comentari correspon a l'ordre diagramàtic. Si la volies així, cal
canviar també (A$^k$3)–(A$^k$6) i (AB$^{l,k}$3). **Recomanació:** mantenir
l'ordre que he posat, que és coherent amb la resta del document.

**B. $\mathrm{tr}_{\mathbf{d}}$ en lloc de $d^\sharp\times d^\sharp$ (punt 2.4).**
És un canvi matemàtic que no demanava el comentari. Sense aquest canvi,
`PEpDerivorFunctor` és falsa per a derivors que «esborren» variables. Una
alternativa és restringir-se a derivors on cada $d(\sigma)$ conté totes les
seues variables i mantenir $d^\sharp\times d^\sharp$. **Recomanació:**
$\mathrm{tr}_{\mathbf{d}}$, que és més general i coincideix amb l'altra opció
en el cas regular.

**C. (GEP1) i (GEP2) són una proposta meua (punt 3).** Les he triat perquè
$\mathbf{d}^*$ siga un functor, i són també necessàries per a això. Si teniu en
ment una altra noció, per exemple sense (GEP1) o amb inclusió, caldrà ajustar
la definició.

**D. Les condicions de domini $D_s$ usen una única variable,** com $\Delta_s(x)$
a [LG18]. Si en algun moment cal que depenguen de més variables, caldria
canviar la definició.

**E. Cas $\omega$ de les especificacions.** No he estés `DVarCompact` a
$\omega$, perquè no és possible (vegeu el punt 5). En canvi, `DVarExtended`
**sí** que es podria estendre a $\omega$: en la presentació estesa no hi ha
condició de finitud, perquè cada cel·la viu en un sort $(k,s)$. No ho he fet
perquè el comentari no ho demanava. Ho proposo com a pas següent.

**F. Notació de variables.** L'Observació `Rdop` numera les variables de
$\downarrow\varphi^\star(\mathbf{s})$ per sorts, com a segments inicials. En
canvi, la secció de les àlgebres de Hall usa $v^{s_j}_j$, per posicions. Per
no prendre partit, he introduït $v^{\mathbf{t}}_j$, «la variable de la lletra
$j$». Caldria unificar les dues convencions algun dia.

**G. El pla de formalització.**
- Els ítems `DSigmaCatCompact` i `DSigmaCatExtended` de `compact.toml` i `extended.toml` estan marcats com a `done`. Ara les definicions inclouen el cas $\omega$, i la compacta també l'estructura d'ep-signatura, que el Lean actual (`compact.signature` i `extended.signature`) no cobreix. El propietari del pla (encosllo) hauria de decidir si cal revisar-los. No he tocat cap fitxer `.toml` ni cap fitxer Lean.
- Els trasllats de definicions no afecten el pla, perquè les referències són etiquetes i no números.
- Les seccions de derivors queden fora de l'abast actual del pla.

## Nous elements del document (etiquetes)

`RGenDerivorSem`, `DEpSignature`, `RSubst`, `DDeft`, `LDeft`, `DCn`,
`DTranslation`, `LTranslation`, `PEpDerivorFunctor`, `REpDerivor`,
`DGenEpDerivor`, `PGenEpDerivorFunctor`, `RGenEpDerivor`, `RCompactEp`.
`DGeneralDerivor` i `DDerivorEP` conserven l'etiqueta, però el contingut és nou.
