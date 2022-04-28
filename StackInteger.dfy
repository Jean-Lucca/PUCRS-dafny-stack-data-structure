class {:autocontracts}  StackInteger
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
    ensures capacity == storage.Length
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

    method Push(e:nat) returns (full: bool)
    ensures stackStorage == old(stackStorage) + [e]
    ensures full ==> stackCapacity == old(capacity) + 10
    {
        //Adicionar um novo elemento no topo da pilha.
        full := top == capacity;
        if full {
            var tmp := new int[capacity + 10];

            forall i | 0 <= i < top
            {
                tmp[i] := storage[i];
            }
            capacity := capacity + 10;
            storage := tmp;
            stackStorage := storage[..top];
            stackCapacity := capacity;
        }
        
        storage[top] := e;
        top := top + 1;
        stackStorage := stackStorage + [e];
    }

    method Pop() returns (e:int)
    requires |stackStorage| > 0
    ensures e == old(stackStorage)[|old(stackStorage)| - 1]
    ensures stackStorage == old(stackStorage)[0..|old(stackStorage)| - 1]
    {
        //Remover um elemento do topo da pilha, caso ela não esteja vazia.
        e := storage[top - 1];
        top := top - 1;
        stackStorage := storage[..top]; 
    }

    method Peek() returns (elem : int)
    requires |stackStorage| > 0
    ensures stackStorage == old(stackStorage)
    ensures elem == stackStorage[|stackStorage| - 1]
    {
        //Ler o valor do topo da pilha, sem removê-lo. 
        elem := storage[top-1];
    }

    method IsEmpty() returns (empty : bool)
    ensures stackStorage == old(stackStorage)
    ensures empty <==> |stackStorage| == 0
    {
        //Verificar se a pilha está vazia ou não, retornando verdadeiro ou falso.
        empty := top == 0; 
    }

    method Size() returns (n:nat)
    ensures stackStorage == old(stackStorage)
    ensures n == |stackStorage|
    {
        //Informar o número de elementos armazenados na pilha. 
        n := top;
    }

    method Invert()
    requires |stackStorage| > 0
    ensures |stackStorage| == |old(stackStorage)|
    ensures forall i | 0 <= i < |stackStorage| :: stackStorage[i] == old(stackStorage[|stackStorage| - i - 1])
    {
        //Inverter a ordem dos elementos da pilha. 
        var tmp := new int[capacity];

        forall i | 0 <= i < top
        {
            tmp[i] := storage[top - i - 1];
        }

        storage := tmp;
        stackStorage := storage[..top];
    }

    // Shows this stack content
    method Show()
    ensures old(stackStorage) == stackStorage
    {
        var size := Size();
        var isEmpty := IsEmpty();
        if(size > 0) 
        {
            var peek := Peek();
            print("\nTop: ",peek);
        }

        print("\nSize: ",size);
        print("\nisEmpty",isEmpty);
        print("\nContent\n");
        print(storage[..top]);
        print("\n");
    }
}

method Main()
{
    var stack := new StackInteger();
    var push,pop;
    push := stack.Push(0);
    print("\nPush: ",push);
    stack.Show();
    pop := stack.Pop();
    print("\nPop: ",pop);
    stack.Show();
    push := stack.Push(1);
    print("\nPush: ",push);
    push := stack.Push(2);
    print("\nPush: ",push);
    push := stack.Push(3);
    print("\nPush: ",push);
    push := stack.Push(4);
    print("\nPush: ",push);
    push := stack.Push(5);
    print("\nPush: ",push);
    push := stack.Push(6);
    print("\nPush: ",push);
    push := stack.Push(7);
    print("\nPush: ",push);
    push := stack.Push(8);
    print("\nPush: ",push);
    push := stack.Push(9);
    print("\nPush: ",push);
    push := stack.Push(10);
    print("\nPush: ",push);
    push := stack.Push(11);
    print("\nPush: ",push);
    push := stack.Push(1);
    print("\nPush: ",push);
    push := stack.Push(2);
    print("\nPush: ",push);
    push := stack.Push(3);
    print("\nPush: ",push);
    push := stack.Push(4);
    print("\nPush: ",push);
    push := stack.Push(5);
    print("\nPush: ",push);
    push := stack.Push(6);
    print("\nPush: ",push);
    push := stack.Push(7);
    print("\nPush: ",push);
    push := stack.Push(8);
    print("\nPush: ",push);
    push := stack.Push(9);
    print("\nPush: ",push);
    push := stack.Push(10);
    print("\nPush: ",push);
    push := stack.Push(11);
    print("\nPush: ",push);
}