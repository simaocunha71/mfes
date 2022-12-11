////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                    Exercício de avaliação (Modelação comportamental com Alloy)                                        
//Nome: Simão Pedro Sá Cunha                                                                                                
//Número: a93262                                                                                                            
//Curso: MIEI                                                                                                               
//                                                                                                                       
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                        Assinaturas
sig Password {}
sig User {
  var password : set Password
}
var sig LoggedIn in User {}
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Comportamento da autenticação
pred behavior {
    // Estados iniciais
    no LoggedIn 
    no password 
    
    // Transições
    always {
      (some u : User, p : Password | criaConta[u, p]) or
      (some u : User, p : Password | apagaConta[u, p]) or
      (some u : User, p : Password | logIn[u, p]) or 
      (some u : User | logOut[u]) or
      (some u : User, p : Password | alteraPassword[u, p]) or
      stutter
    }
}

// Cria-se uma conta para o utilizador
pred criaConta[u : User, p : Password]{  
  historically no u.password
  password' = password + (u->p)
  LoggedIn' = LoggedIn + u
  u.password' = u.password + p
}

// Apaga-se a conta de um utilizador
pred apagaConta[u : User, p : Password]{
  u in LoggedIn
  p = u.password
  password' = password - (u->p)
  LoggedIn' = LoggedIn - u
  u.password' = u.password - p
}

// Utilizador faz log in
pred logIn[u : User, p : Password] {
  u not in LoggedIn
  p = u.password
  password' = password
  LoggedIn' = LoggedIn + u
}

// Utilizador faz log out
pred logOut[u : User] {
  password' = password
  LoggedIn' = LoggedIn - u
}

// Utilizador altera password
pred alteraPassword[u : User, newPass : Password]{
  historically newPass not in u.password
  u in LoggedIn
  password' = password - (u->u.password) + (u->newPass)
  LoggedIn' = LoggedIn
}

// Stuttering
pred stutter { 
  password' = password
  LoggedIn' = LoggedIn
}