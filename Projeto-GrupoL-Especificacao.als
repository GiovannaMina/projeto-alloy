-- SISTEMA PENITENCIÁRIO

-- ASSINATURAS
sig Guarda {}

abstract sig Cela {
	detentos: set Detento,
	guarda: lone Guarda
}

some sig CelaComum extends Cela {}
some sig Solitaria extends Cela {}

abstract sig Detento {
	cela: one Cela
}

some sig DetentoComum extends Detento {}
some sig DetentoPerigoso extends Detento {}

-- REGRAS

fact {

	-- F1: Consistência bidirecional entre detento e cela
	-- Um detento está em uma cela se e somente se essa cela lista esse detento
	all d: Detento, c: Cela |
		d in c.detentos <=> d.cela = c

	-- F2: Detento perigoso só pode ficar em solitária
	all d: DetentoPerigoso | detento_perigoso_em_solitaria[d]

	-- F3: Cela comum tem no máximo 4 detentos
	all c: CelaComum | capacidade_cela_comum[c]

	-- F4: Solitária tem no máximo 1 detento
	all s: Solitaria | capacidade_solitaria[s]

	-- F5: Toda cela ocupada deve ter exatamente um guarda
    all c: Cela | #c.detentos > 0 implies one c.guarda

	-- F6: Cela vazia não deve ter guarda
    all c: Cela | #c.detentos = 0 implies no c.guarda
}

-- PREDICADOS

-- Um detento comum pode ficar em cela comum OU solitária
pred detento_comum_flexivel[d: DetentoComum] {
    d.cela in CelaComum or d.cela in Solitaria
}

-- Um detento perigoso deve estar em uma solitária
pred detento_perigoso_em_solitaria[d: DetentoPerigoso] {
	d.cela in Solitaria
}

-- Cela comum comporta no máximo 4 detentos
pred capacidade_cela_comum[c: CelaComum] {
	#c.detentos <= 4
}

-- Solitária comporta no máximo 1 detento
pred capacidade_solitaria[s: Solitaria] {
	#s.detentos <= 1
}

-- Cela ocupada tem exatamente um guarda responsável
pred guarda_em_cela_ocupada[c: Cela] {
	one c.guarda

	-- FORMAS (equivalentes):
	-- #c.guarda = 1
	-- some g: Guarda | c.guarda = g
}

-- Cela vazia não tem guarda alocado
pred cela_vazia_sem_guarda[c: Cela] {
	no c.guarda

	-- FORMAS (equivalentes):
	-- #c.guarda = 0
	-- c.guarda = none
}

-- Um guarda é responsável por mais de uma cela
pred guarda_multiplas_celas[g: Guarda] {
	#{ c: Cela | c.guarda = g } > 1
}

-- Uma solitária está com lotação máxima 
pred solitaria_cheia[s: Solitaria] {
    #s.detentos = 1
}

-- Uma cela comum está com lotação máxima
pred cela_comum_cheia[c: CelaComum] {
	#c.detentos = 4
}

-- ASSERÇÕES

-- A1: Toda cela comum tem no máximo 4 detentos
assert adicionar_detento_cela_comum_cheia {
	all c: CelaComum | #c.detentos <= 4
}
check adicionar_detento_cela_comum_cheia for 10

-- A2: Toda solitária tem no máximo 1 detento
assert adicionar_detento_perigoso_solitaria_cheia {
	all s: Solitaria | #s.detentos <= 1
}
check adicionar_detento_perigoso_solitaria_cheia for 10

-- A3: Nenhum detento perigoso está em cela comum
assert adicionar_detento_perigoso_cela_comum {
	no d: DetentoPerigoso | d.cela in CelaComum
}
check adicionar_detento_perigoso_cela_comum for 10

-- A4: Cela vazia nunca tem guarda
assert adicionar_guarda_cela_vazia {
	all c: Cela | no c.detentos implies no c.guarda
}
check adicionar_guarda_cela_vazia for 10

-- A5: Cela ocupada tem exatamente um guarda
assert adicionar_multiplos_guardas_cela_ocupada {
	all c: Cela | #c.detentos > 0 implies one c.guarda
}
check adicionar_multiplos_guardas_cela_ocupada for 10
-- CENÁRIOS

-- EXISTENTES
-- C1: Simula um presídio completo. 
pred simulacao_presidio_completo {
    some g: Guarda | guarda_multiplas_celas[g]
    some c: CelaComum | cela_comum_cheia[c]
    some d: DetentoPerigoso | detento_perigoso_em_solitaria[d]
    
    -- FORMA 2 (Equivalente):
    -- some g: Guarda, c: CelaComum, s: Solitaria, d: DetentoPerigoso | 
    --    #g.celas > 1 and #c.detentos = 3 and d in s.detentos
}
run simulacao_presidio_completo for 6

-- C2: Simula uma solitaria tem um detento.
pred solitaria_com_um_detento{
	some s: Solitaria, d: DetentoPerigoso |
		d in s.detentos

    
    -- FORMA 2 (Equivalente):
    -- some s: Solitaria | #s.detentos = 1
}
run solitaria_com_um_detento


-- C3: Simula uma cela comum com um preso.
pred celaComum_com_um_detento{
	some c: CelaComum, d: Detento|
		d in c.detentos

	-- FORMA 2 (equivalente):
    -- some d: Detento | d.cela in CelaComum
}
run celaComum_com_um_detento

-- C4: Simula um preso flexivel na solitaria.
pred solitaria_com_um_detento_flexivel{
	some s: Solitaria, d: DetentoComum|
		d in s.detentos
	-- FORMA 2 (equivalente):
    -- some s: Solitaria | some (s.detentos & DetentoComum)
}
run solitaria_com_um_detento_flexivel

-- C5: Simula uma cela vazia sem guarda.
pred cela_Vazia_sem_guarda{
	some c: Cela | cela_vazia_sem_guarda[c]
    -- FORMA 2 (equivalente):
    -- some c: Cela | cela_vazia_sem_guarda[c]
   

}
run cela_Vazia_sem_guarda

-- C6: Simula um guarda em multiplas celas.
pred guarda_em_multiplas_celas{
	one g: Guarda | guarda_multiplas_celas[g]

    -- FORMA 2 (equivalente):
    -- some g: Guarda | #g.celas > 1

    -- FORMA 3 (equivalente):
    -- some g: Guarda, c1, c2: Cela | c1 in g.celas and c2 in g.celas and c1 != c2
}
run guarda_em_multiplas_celas

-- C7: Simula cela comum com capacidade maxima
pred cela_capacidade_maxima{
	one c: CelaComum | cela_comum_cheia[c]

    -- FORMA 2 (equivalente):
    -- some c: CelaComum | #c.detentos = 3

    -- FORMA 3 (equivalente):
    -- all d: Detento | d in c.detentos implies #c.detentos = LimiteMaximo

}
run cela_capacidade_maxima for 5

-- C8: Simula cela nao cheia
pred cela_comum_vagas_sobrando {
    some c: CelaComum | some c.detentos and not cela_comum_cheia[c]

    -- FORMA 2 (equivalente):
    -- some c: CelaComum | #c.detentos > 0 and #c.detentos < 3
}
run cela_comum_vagas_sobrando


-- INEXISTENTES
-- C1: Simula uma cela com 5 detentos.
pred cela_comum_superlotada{
	some c: CelaComum | #c.detentos > 4
    
    -- FORMA 2 (equivalente):
    -- run { some c: CelaComum | #c.detentos = 5 } for 5
}
run cela_comum_superlotada

-- C2: Solitaria superlotada.
pred solitaria_superlotada{
    some s: Solitaria | #s.detentos > 1
 
    -- FORMA 2 (equivalente):
    -- some s: Solitaria, d1, d2: Detento | d1 in s.detentos and d2 in s.detentos and d1 != d2
}
run solitaria_superlotada

-- C3: Simula um detento perigoso em uma cela comum.
pred detento_perigoso_em_cela_comum{
	some c: CelaComum, d: DetentoPerigoso |
		d in c.detentos

    -- FORMA 2 (equivalente):
    -- some (CelaComum.detentos & DetentoPerigoso)
}
run detento_perigoso_em_cela_comum

-- C4: Simula um guarda sem cela.
pred guarda_sem_cela {
  one c: Cela, d: Detento| 
	cela_vazia_sem_guarda[c] and d in c.detentos
    -- FORMA 2 (equivalente):
    -- #Guarda > #Guarda.celas
}
run guarda_sem_cela


-- C5: Simula cela com multiplos guardas.
pred cela_com_multiplos_guardas {
    some c: Cela | #c.guarda > 1

    -- FORMA 2 (equivalente):
    -- some c: Cela, g1, g2: Guarda | g1 in c.guarda and g2 in c.guarda and g1 != g2
}
run cela_com_multiplos_guardas

pred detento_sem_cela {
    some d: Detento | no c: Cela | d in c.detentos

    -- FORMA 2 (equivalente):
    -- some d: Detento | d !in Cela.detentos
}
run detento_sem_cela
