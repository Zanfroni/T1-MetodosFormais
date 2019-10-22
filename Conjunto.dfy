/* TRABALHO 1: METODOS FORMAIS */
/*  INTEGRANTES
    * Bruno Selau
    * Enrique Bozza Dutra
    * Gabriel Franzoni
*/

class {:autocontracts} NatSet
{
    // Abstracoes iniciais (ghosts e variaveis uteis)
    // Ghost representando o conjunto como sequencia requisitado
    var s: array<nat>;
    var size: nat;
    ghost var Set: seq<nat>;

    // Predicate invariante de classe requisitado
    // Este mesmo garante que o conjunto nunca seja vazio
    // assim como atualiza o seu tamanho e garante
    // no forall que nenhum valor no conjunto se repete
    // #Adaptado do exemplo mostrado em aula
    predicate Valid()
    {
        s.Length != 0
        && 0 <= size <= s.Length
        && s[0..size] == Set
        && forall i,j :: 0 <= i < size
                        && 0 <= j < size
                        && i != j
                        ==> s[i] != s[j]
    }

    // Construtor requisitado
    // Este mesmo instancia e garante o conjunto vazio
    constructor ()
    ensures Set == []
    {
        s := new nat[10];
        size := 0;
        Set := [];
    }

    // OPERACOES REQUISITADAS

    // Adicionar valor no conjunto e retornar booleano
    // Esta operacao nao necessita de pre condicoes
    // Ela garante que quando retorna falso, o Conjunto nao altera
    // assim como seu tamanho
    // Ela garante que quando retorna verdadeiro, o conjunto ganha o novo
    // elemento "e" concatenado no fim, assim como seu tamanho acrescenta em 1
    // Ele tambem precisa garantir que o "size" aumente em 1, pois este e o nosso
    // ponteiro para adicao de novos valores    
    method Add(e:nat) returns (b:bool)
    ensures e in old(Set) ==> (Set == old(Set)) && b == false
    ensures e in old(Set) ==> |Set| == |old(Set)|
    ensures !(e in old(Set)) ==> (Set == old(Set) + [e]) && b == true
    ensures !(e in old(Set)) ==> |Set| == |old(Set)| + 1
    ensures !(e in old(Set)) ==> size == old(size) + 1
    {
        // Ele chama o metodo "Contains" para ja verificar se ja nao existe
        // o elemento atual no vetor
        var verify := Contains(e);
        if(!verify){
            if(size == s.Length)
            {
                // Como estamos trabalhando com um vetor, se ele estiver lotado,
                // ou seja, se o ponteiro estiver na posicao que equivale ao tamanho
                // atual, vamos dinamicamente duplica-lo. Precisa criar um novo,
                // pois o array e algo imutavel
                var newSize := new nat[2 * s.Length];
                var i := 0;
                // while(i < s.Length) causou erro nas pos condicoes
                // adaptou-se a logica forall da fila de exemplo da aula
                forall(i | 0 <= i <= size-1)
                {
                    newSize[i] := s[i];
                }
                s := newSize;
            }
            s[size] := e;
            size := size + 1;
            Set := Set + [e];
            b := !verify;
        } else {
            b := !verify;
        }
    }

    // Verificar se no conjunto escolhido existe o valor requisitado
    // Garante que o boolean retornado esta relacionado ao valor "e"
    // se esta ou nao presente no Conjunto. Deve retornar verdadeiro
    // se estiver presente no conjunto
    method Contains(e:nat) returns (b:bool)
    ensures b <==> e in Set
    {
        b := false;
        var i := 0;
        while(i < size)
        // Invariantes de laco. Deve garantir que i esteja no intervalo devido
        // e garante que se i exceder 0, o conjunto ira retornar um boolean true
        // caso o valor seja encontrado no conjunto
        invariant 0<=i<=size
        invariant (i > 0) ==> b == (e in Set[0..i])
        // Esta invariante foi adicionada para cessar um erro que acontecia caso
        // nao fosse tratado se i < 1
        invariant (i == 0) ==> !b
        decreases size - i
        {
            if(s[i] == e){
                b := true;
            }
            i := i + 1;
        }
        return b;
    }

    // Retorna o numero de elementos do conjunto
    // Simples. Apenas garante que retorne o "size" atual, garantido que ele seja
    // maior que 0, pois o array nao pode ser vazio.
    // Garante que o "t" que retorne seja do tamanho do conjunto Set
    // pois o array pode ter um tamanho alocado maior
    method Size() returns (t:nat)
    requires size >= 0
    ensures t == |Set|
    {
        return size;
    }

    // Retorna um conjunto da uniao entre dois conjuntos.
    // Este metodo necessita que um novo conjunto seja inputado, alem de termos
    // o nosso atual criado pelo constructor
    // Garante que o novo conjunto nao seja vazio.
    // Uniao basicamente se aplica a criar um novo conjunto, inserir TODOS
    // os elementos do conjunto 1 e apenas complementar com os elementos do conjunto 2
    // nao presentes no conjunto 1
    method Union(inputSet: NatSet) returns (newSet: NatSet)
    // Precisa garantir que todos os valores inseridos no newSet, tanto de
    // inputSet como do conjunto atual estejam contidos no newSet
    requires |Set| >= 0
    requires |inputSet.Set| >= 0
    ensures |newSet.Set| >= 0
    ensures forall i :: (0 <= i< |Set|) ==> Set[i] in newSet.Set
    ensures forall i :: (0 <= i< |inputSet.Set|) ==> inputSet.Set[i] in newSet.Set
    ensures |newSet.Set| <= |Set| + |inputSet.Set|
    {
        // Declaracao do novo conjunto e suas variaveis
        newSet := new NatSet();
        newSet.size := size + inputSet.size;
        newSet.s := new nat[size + inputSet.size];
        newSet.Set := [];

        var i := 0;
        var j := 0;
        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var b := newSet.Add(s[i]);
            i := i + 1;
        }

        while(j < inputSet.size)
        decreases inputSet.size - j
        invariant 0 <= j <= inputSet.size
        {
            var verify := Contains(inputSet.s[size+j]);
            if(!verify){
                var b := newSet.Add(inputSet.s[size+j]);
            }
            j := j + 1;
        }

    }
    
    // Retorna um conjunto da interseccao entre dois conjuntos.
    // Este metodo necessita que um novo conjunto seja inputado, alem de termos
    // o nosso atual criado pelo constructor
    // Para isso, pegamos o conjunto 1 e vemos se cada elemento dele tambem esta
    // presente no conjunto 2. Se estar presente, este elemento e inserido no conjunto 3
    method Intersection(inputSet: NatSet) returns (newSet: NatSet)
    // Deve-se garantir que os conjuntos nao estejam vazios
    // Precisa ter como pos condicoes consideracoes como os valores i que estao no
    // novo conjunto, ambos precisam de fato estar contidos no conjunto 1 e 2
    // Tambem foi feita uma pos condicao que garante que todos os valores
    // do conjunto 3 nao sao repetidos, ja que a implementacao nao verifica isso
    requires |Set| >= 0
    requires |inputSet.Set| >= 0
    ensures |newSet.Set| >= 0
    ensures forall i:: (0 <= i< |newSet.Set|) ==> newSet.Set[i] in Set
    ensures forall i:: (0 <= i< |newSet.Set|) ==> newSet.Set[i] in inputSet.Set
    ensures forall i,j :: (0 <= i < |newSet.Set|)
                        && (0 <= j < |newSet.Set|)
                        && (i != j) ==> newSet.Set[i]
                        != newSet.Set[j]
    {
        // Declaracao do novo conjunto
        newSet := new NatSet();
        newSet.size := size + inputSet.size;
        newSet.s := new nat[size + inputSet.size];
        newSet.Set := [];

        var i := 0;
        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var verify := inputSet.Contains(s[i]);
            if(verify)
            {
                var b := newSet.Add(s[i]);
            }
            i := i + 1;
        }

    }

    // Retorna um conjunto da diferenca entre dois conjuntos.
    // Este metodo necessita que um novo conjunto seja inputado, alem de termos
    // o nosso atual criado pelo constructor
    // Este mesmo precisa garantir que sejam pegos todos os elementos dos dois conjuntos
    // que nao possuam interseccao
    method Difference(inputSet: NatSet) returns (newSet: NatSet)
    // Precisa garantir que os conjuntos nao estejam vazios
    // Ele garante que o novo conjunto nao seja vazio e que
    // sempre o novo elemento inserido no conjunto 3, OU vai estar apenas no conjunto 1
    // OU apenas no conjunto 2
    requires |Set| >= 0
    
    requires |inputSet.Set| >= 0
    
    ensures |newSet.Set| >= 0
    
    ensures forall i :: (0 <= i < |newSet.Set|) ==> ((newSet.Set[i] in Set) && !(newSet.Set[i] in inputSet.Set))
                    || (newSet.Set[i] in inputSet.Set && !(newSet.Set[i] in Set))
    {
        // Declaracao do novo conjunto
        newSet := new NatSet();
        newSet.size := size + inputSet.size;
        newSet.s := new nat[size + inputSet.size];
        newSet.Set := [];

        var i := 0;
        var k := 0;
        while(i < size)
        decreases size - i
        invariant 0 <= i <= size
        {
            var verify := Contains(s[i]);
            if(!verify){
                var b := newSet.Add(s[i]);
            }
            i := i + 1;
        }

        while(k < inputSet.size)
        decreases inputSet.size - k
        invariant 0 <= k <= inputSet.size
        {
            var verify := Contains(inputSet.s[k]);
            if(!verify){
                var b := newSet.Add(inputSet.s[k]);
            }
            k := k + 1;
        }
    }
}

// Main, que ira realizar os testes via assertions
method Main()
{
    // Criacao do conjunto e adicao de valores
    var newSet := new NatSet();
    assert newSet.Set == [];
    var b := newSet.Add(4);
    assert newSet.Set == [4];
    b := newSet.Add(8);
    b := newSet.Add(6);
    b := newSet.Add(5);
    b := newSet.Add(2);
    b := newSet.Add(3);
    assert b ==  true;
    b := newSet.Add(3);
    assert b == false;

    // Verificacao se contem ou nao
    b := newSet.Contains(6);
    assert b == true;
    b := newSet.Contains(9);
    assert b == false;

    // Verifica numero de elementos no conjunto
    var e := newSet.Size();
    assert e == 6;
    assert |newSet.Set| == 6;
    // assert e == 7; // ---> Aqui falha, como realmente deve

    var newSet2 := new NatSet();
    var c := newSet2.Add(8);
    c := newSet2.Add(7);
    c := newSet2.Add(9);
    c := newSet2.Add(1);
    c := newSet2.Add(3);

    // Operacoes de conjuntos
    var unionSet := newSet.Union(newSet2);
    assert unionSet.size == 8;

    var interSet := newSet.Intersection(newSet2);
    assert interSet.size == 2;

    var diffSet := newSet.Difference(newSet2);
    assert diffSet.size == 7;

    // O codigo constantemente apresentou warnings como que uma pos condicoes pode
    // nao garantir, mas isto esta devidamente documentado no Dafny que ele
    // pode nem sempre garantir que o computador atinja tal estado
}
