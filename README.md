# Sistema de Alocação Penitenciária

Este repositório contém o projeto final da disciplina de Lógica para Computação. Ele consiste em um modelo formal desenvolvido na linguagem Alloy para o gerenciamento e alocação de recursos em uma penitenciária.

## Objetivo do Projeto

Devido a uma crescente onda de crimes e ao aumento do número de detentos em uma penitenciária, o controle manual de alocação de guardas e celas tornou-se inviável. 

O objetivo desse projeto é implementar um sistema capaz de armazenar, gerenciar e validar a alocação de celas e guardas de forma segura e consistente, garantindo que todas as regras de segurança e capacidade do presídio sejam respeitadas.

## Como o Projeto Funciona

O sistema foi modelado utilizando lógica relacional e de primeira ordem através da linguagem Alloy. Ele é dividido em Assinaturas, Fatos, Predicados e Asserções, e Casos de Teste (Cenários).

### Entidades Principais (`sig`)
* **Guarda:** Responsável pela vigilância das celas. Um mesmo guarda pode supervisionar mais de uma cela.
* **Cela:** Estrutura abstrata de confinamento, dividida em:
    * `CelaComum`: Capacidade máxima de 4 detentos.
    * `Solitaria`: Capacidade máxima de 1 detento.
* **Detento:** Indivíduos alocados nas celas, classificados pelo nível de periculosidade:
    * `DetentoComum`: Pode ser alocado em celas comuns ou em solitárias.
    * `DetentoPerigoso`: Deve ser alocado em celas solitárias.

### Regras (`fact`)
O modelo garante a consistência do sistema aplicando as seguintes regras:
1.  **Consistência Bidirecional:** Um detento está em uma cela se, e somente se, aquela cela lista o detento em seus registros.
2.  **Isolamento de Periculosidade:** Todo detento classificado como "perigoso" obrigatoriamente ocupa uma solitária.
3.  **Controle de Lotação:** Celas comuns comportam no máximo 4 detentos, e solitárias comportam no máximo 1 detento.
4.  **Alocação de Guardas:**
    * Toda cela ocupada possui exatamente um guarda responsável em tempo integral.
    * Celas vazias não possuem guardas alocados.

### Testes e Verificações (`assert` e `pred`)
O código inclui asserções para verificar se o modelo permite estados inválidos (ex: superlotação, detentos perigosos em celas comuns, guardas em celas vazias). Além disso, foram modelados diversos cenários que o Alloy Analyzer tenta instanciar para comprovar a lógica do sistema.

## Como Rodar o Código

Para executar e visualizar os modelos gerados por este projeto, siga os passos abaixo:

1.  **Pré-requisitos:**
    * Instale a extensão Alloy no VS Code .
    * Certifique-se de ter o Java (JRE/JDK) instalado em sua máquina, pois o motor do Alloy depende dele.

2.  **Execução:**
    * Clone este repositório
    * Abra a pasta do projeto no VS Code.
    * Abra o arquivo `.als` contendo o código do sistema.
    * Você verá opções como `Execute` ou `Check` acima de cada comando `run` ou `check`.
    * Clique em **`run <nome_do_cenario>`** para gerar uma instância válida daquele cenário.
    * Clique em **`check <nome_da_assercao>`** para garantir que nenhuma regra foi violada (o ideal é que o console retorne *No counterexample found*).

## Ferramentas

* **Alloy:** Linguagem de modelagem baseada em lógica de primeira ordem.
* **Visual Studio Code:** Ambiente de Desenvolvimento Integrado.
* **Git / GitHub:** Controle de versão e hospedagem do repositório.

## Integrantes

* Camila Gomes dos Santos
* Clarice Leite Rangel
* Giovanna Farias Miná
* Laís Ferreira Lira
* Natalia Rodrigues da Silva
* Maria Luisa

## Componente Curricular
* Disciplina: Lógica para Computação
* Professores: Salatiel Dantas Silva e Maxwell Guimarães de Oliveira
* Período: 2025.2
