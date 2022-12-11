/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                    Exercício de avaliação (Modelação estrutural com Alloy)                                        
//Nome: Simão Pedro Sá Cunha                                                                                                
//Número: a93262                                                                                                            
//Curso: MIEI                                                                                                               
//                                                                                                                          
//Links onde fui consultar informação acerca das red black trees:                                                           
//-> https://www.geeksforgeeks.org/red-black-tree-set-1-introduction-2/                                                     
//-> https://en.wikipedia.org/wiki/Red-black_tree                                                                           
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                        Assinaturas                                                                     
sig Node {                                                                                                                       
    children : set Node                                                                                                          
}                                                                                                                                
sig Leaf extends Node {}                                                                                                         
one sig Root in Node {}                                                                                                          
                                                                                                                                 
sig Red, Black in Node {}                                                                                                        
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                        Invariantes                                                                     
pred Invs {                                                                                                                      
    //Os nós deste tipo de árvore ou são de cor vermelha ou de cor preta                                                         
    //Nota: usei o equivalente em Alloy o equivalente o XOR (exclusive OR)                                                       
    all n : Node | n in Red iff not n in Black                                                                                   
                                                                                                                                 
    //A raíz tem de ser de cor preta                                                                                             
    all r : Root | r in Black                                                                    
                                                                                                                                 
    //Todas as travessias desde um nó até a qualquer um dos seus descendentes tem o mesmo número de nós pretos                   
    //Nota: por uma questão de comodidade, decidi percorrer desde uma leaf até a um certo nó da árvore hierarquicamente acima,   
    //o que acaba por ser o mesmo raciocínio                                                                                     
    all l1,l2 : Leaf | #(Black & ^(children).l1) = #(Black & ^(children).l2)                                                     
                                                                                                                                 
    //Todas as folhas são de cor preta (e também não têm filhos)                                                                 
    all l : Leaf | l in Black and #l.children = 0                                                                                
                                                                                                                                 
    //Todos os filhos de um nó devem estar abaixo na hierarquia da árvore                                                        
    all n : Node | n not in n.^(children)                                                                                        
                                                                                                                                 
    //Todos os nós devem ser alcançados desde a raíz                                                                             
    all n : Node | n in Root.*(children)                                                                                         
                                                                                                                                 
    //Filhos vermelhos têm sempre filhos pretos                                                                                  
    all r : Red | r.children in Black and not r.children in Red                                                                  
                                                                                                                                 
    //Todos os nós (exceto a raíz) deve ter apenas um único pai                                                                  
    //Esta regra é necessária para evitar casos em que, por exemplo, um filho da raíz é um pai do outro filho da mesma raíz      
    all n : Node - Root | one children.n                                                                                         
    no children.Root                                                                                                             
                                                                                                                                 
    //Todos os nós (exceto as leafs) devem ter 2 filhos                                                                          
    all n : Node-Leaf | #n.children = 2                                                                                          
}                                                                                                                                
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////