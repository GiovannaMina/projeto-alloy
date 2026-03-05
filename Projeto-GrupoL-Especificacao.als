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

	-- F2: Detento comum só pode ficar em cela comum
	all d: DetentoComum | detento_comum_em_cela_comum[d]

	-- F3: Detento perigoso só pode ficar em solitária
	all d: DetentoPerigoso | detento_perigoso_em_solitaria[d]

	-- F4: Cela comum tem no máximo 4 detentos
	all c: CelaComum | capacidade_cela_comum[c]

	-- F5: Solitária tem no máximo 1 detento
	all s: Solitaria | capacidade_solitaria[s]

	-- F6: Toda cela ocupada deve ter exatamente um guarda
	all c: Cela | #c.detentos > 0 => guarda_em_cela_ocupada[c]

	-- F7: Cela vazia não deve ter guarda
	all c: Cela | #c.detentos = 0 => cela_vazia_sem_guarda[c]

}
