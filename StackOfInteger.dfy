class {:autocontracts}  StackOfInteger
{
    //Representação abstrata:
    ghost var stackStorage: seq<int>
    ghost var stackCapacity: nat

    //Implementação
    var storage: array<int>;
    var capacity: nat;
    var top: nat;

    predicate Valid()
    {
        //Utilizar um predicado adequado para a invariante da representação abstrata associada 
        //à coleção do tipo pilha. 
        capacity > 0
        && storage.Length == capacity
        && 0 <= top <= capacity
        && stackCapacity == capacity
        && stackStorage == storage[0..top]
    }

    constructor()
    ensures stackStorage == []
    ensures top == 0
    {
        //Construtor deve instanciar uma pilha vazia
        capacity := 10;
        top := 0;
        storage := new int[10];
        
        stackStorage := [];
        stackCapacity := capacity;
    }

    //Adicionar um novo elemento no topo da pilha.
    method Push(e:nat) returns (elem: int)
    ensures stackStorage == old(stackStorage) + [e]
    ensures stackStorage[0..top] == old(stackStorage[0..top]) + [e]
    ensures elem == stackStorage[|stackStorage| - 1]
    ensures top == old(top) + 1
    {
        var full := top == capacity;
        if full
        {
            var newCapacity := capacity + 10;
            var newStorage := new int[newCapacity];

            forall i | 0 <= i < top
            {
                newStorage[i] := storage[i];
            }

            capacity := newCapacity;
            storage := newStorage;
            stackStorage := storage[..top];
            stackCapacity := capacity;
        }
        
        storage[top] := e;
        top := top + 1;
        stackStorage := stackStorage + [e];
        elem := e;
    }

    //Remover um elemento do topo da pilha, caso ela não esteja vazia.
    method Pop() returns (e:int)
    requires |stackStorage| > 0
    ensures e == old(stackStorage)[|old(stackStorage)| - 1]
    ensures stackStorage == old(stackStorage)[0..|old(stackStorage)| - 1]
    ensures top == old(top) - 1
    {
        e := storage[top - 1];
        top := top - 1;
        stackStorage := storage[..top]; 
    }

    //Ler o valor do topo da pilha, sem removê-lo. 
    method Peek() returns (elem : int)
    requires |stackStorage| > 0
    ensures stackStorage == old(stackStorage)
    ensures elem == stackStorage[|stackStorage| - 1]
    {
        elem := storage[top-1];
    }

    //Verificar se a pilha está vazia ou não, retornando verdadeiro ou falso.
    method IsEmpty() returns (empty : bool)
    ensures stackStorage == old(stackStorage)
    ensures empty <==> |stackStorage| == 0
    {
        empty := top == 0; 
    }

    //Informar o número de elementos armazenados na pilha. 
    method Size() returns (n:nat)
    ensures stackStorage == old(stackStorage)
    ensures n == |stackStorage|
    {
        n := top;
    }

    //Inverter a ordem dos elementos da pilha. 
    method Invert()
    ensures |stackStorage| == |old(stackStorage)|
    ensures forall i | 0 <= i < |stackStorage| :: stackStorage[i] == old(stackStorage[|stackStorage| - i - 1])
    {
        var tmp := new int[capacity];

        forall i | 0 <= i < top
        {
            tmp[i] := storage[top - i - 1];
        }

        storage := tmp;
        stackStorage := storage[..top];
    }
}

method Main()
{
    var stack := new StackOfInteger();
    var isEmpty := stack.IsEmpty();
    var size := stack.Size();
    assert isEmpty == true;
    assert size == 0;

    var addedElement := stack.Push(0);
    var topElement := stack.Peek();

    isEmpty := stack.IsEmpty();
    size := stack.Size();

    assert isEmpty == false;
    assert size == 1;
    assert topElement == 0;
    assert topElement == addedElement;

    var removedElement := stack.Pop();
    isEmpty := stack.IsEmpty();
    size := stack.Size();

    assert isEmpty == true;
    assert size == 0;
    assert removedElement == 0;

    addedElement := stack.Push(0);
    addedElement := stack.Push(1);
    addedElement := stack.Push(2);
    addedElement := stack.Push(3);
    addedElement := stack.Push(4);
    addedElement := stack.Push(5);
    addedElement := stack.Push(6);
    addedElement := stack.Push(7);
    addedElement := stack.Push(8);
    addedElement := stack.Push(9);
    addedElement := stack.Push(10);
    addedElement := stack.Push(11);
    addedElement := stack.Push(12);

    topElement := stack.Peek();
    isEmpty := stack.IsEmpty();
    size := stack.Size();

    assert isEmpty == false;
    assert size == 13;
    assert topElement == 12;
    assert topElement == addedElement;

    print(stack.storage[..stack.top]);

    var oldTopElement := topElement;
    removedElement := stack.Pop();
    assert oldTopElement == removedElement;

    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();
    removedElement := stack.Pop();

    print(stack.storage[..stack.top]);

    isEmpty := stack.IsEmpty();
    size := stack.Size();

    assert isEmpty == true;
    assert size == 0;
    assert removedElement == 12;
}
