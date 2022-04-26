//Pilha sem limite de tamanho de inteiros

/*
Todas  as  pré-condições,  pós-condições, invariantes  e  variantes  devem  ser  corretamente 
especificadas. Faz parte da avaliação do trabalho o completo entendimento de quais asserções 
devem fazer parte da especificação das operações solicitadas. 
*/

//Utilizar o suporte de autocontratos para simplificar a especificação em Dafny. 
class {:autocontracts}  StackInteger
{
    //Implementação
    //var a: array<nat>;
    //var cauda: nat;

    //Representação abstrata (via ghost): 
    //Representar a coleção de elementos da pilha. 
    //ghost var Conteudo: seq<nat>;

    predicate Valid()
    {
        //Utilizar um predicado adequado para a invariante da representação abstrata associada 
        //à coleção do tipo pilha. 
        true
    }

    //Operações
    constructor (m:nat)
    {
        //Instanciar uma pilha vazia
    }

    method Push(e:nat)
    {
        //Adicionar um novo elemento no topo da pilha.
    }

    method Pop() returns (e:nat)
    {
        //Remover um elemento do topo da pilha, caso ela não esteja vazia. 
    }

    method Peek() returns (elem : int)
    {
        //Ler o valor do topo da pilha, sem removê-lo. 
    }

    method IsEmpty() returns (empty : bool)
    {
        //Verificar se a pilha está vazia ou não, retornando verdadeiro ou falso. 
    }

    method Size() returns (n:nat)
    {
        //Informar o número de elementos armazenados na pilha. 
    }

    method Reverse()
    {
        //Inverter a ordem dos elementos da pilha. 
    }
    
}

method Main()
{
}