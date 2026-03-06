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
	-- F1: Bidirecional entre detento e cela
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
	all c: Cela | #c.detentos > 0 => guarda_em_cela_ocupada[c]

	-- F6: Cela vazia não deve ter guarda
	all c: Cela | #c.detentos = 0 => cela_vazia_sem_guarda[c]

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

	-- FORMA 2 (equivalente):
	-- #c.guarda = 1

	-- FORMA 3 (equivalente):
	-- some g: Guarda | c.guarda = g
}

-- Cela vazia não tem guarda alocado
pred cela_vazia_sem_guarda[c: Cela] {
	no c.guarda

	-- FORMA 2 (equivalente):
	-- #c.guarda = 0

	-- FORMA 3 (equivalente):
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