#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Mon May 13 10:55:15 2019

@author: smc
"""

"""
Calculates the size of the union of the variables of all the tables in a list
"""

from tablaClausulas import *
from vartablasd import *

def tam(l):
    tot = set()
    if l:
        for h in l:
            tot.update(set(h.listavar))
        return len(tot)
    else:
        return 0    

def valord(p):
    if not len(p.listavar)==1:
        print("llamada impropia")
    else:
        v = p.listavar[0]
        if not p.tabla[0]:
            return v
        else:
            return -v

def contenida(nodo, listanodos):
    if (len(listanodos)>0):
        nodoaux = nodoTabla([])
        for x in range(len(listanodos)):
            nodoaux.combina(listanodos[x], inplace=True)
        listaBorra = list(set(nodoaux.listavar)-set(nodo.listavar))
        nodoaux.borra(listaBorra, inplace=True)
        nodoaux.tabla = np.logical_not(nodoaux.tabla)
        nodoaux=nodoaux.suma(nodo)
        return nodoaux.trivial()
    else:
        return False

def partev(lista,v):
    bor = []
    nl = []
    for p in lista:
        if p.trivial():
            bor.append(p)
            # print("trivial antes ")
             
        elif v in p.listavar:
            l = p.descomponev(v)
            if len(l)>1:
                for q in l:
                    if not q.trivial():
                        nl.append(q)
                    # else:
                        # print("trivial ", q.listavar)
                bor.append(p)
                # print("descomposicion ", len(p.listavar))
                # print([len(q.listavar) for q in l])
                # sleep(1)
            
    for p in bor:
        lista.remove(p)
    lista.extend(nl)

    lista.sort(key = lambda x : len(x.listavar) )


def potdev(v):
    res = nodoTabla([abs(v)])
    if v>0:
        res.tabla[0] = False
    else:
        res.tabla[1] = False
    return res


def getclusters(lista):
    li = [set(q.getvars()) for q in lista]
    borraincluidos(li)
    return li

def calculaclusters1(lista,p,var):
    li = [set(q.listavar).union(p.listavar) - {var} for q in lista]
    borraincluidos(li)
    return li

def calculaclusters2(lista,var):
    li = []
    for p in lista:
        s = set(p.getvars())
        for q in lista:
            li.append(s.union(q.listavar)- {var})
    borraincluidos(li)
    return li

def borraincluidos(lista):
    
    lista.sort(key = lambda x : - len(x) )

    
    i=0
    while i <len(lista)-1:
        j = i+1
        while j < len(lista):
            con1 = lista[i]
            con2 = lista[j]
            if con2 <= con1:
                lista.remove(con2)
            else:
                j+=1
        i += 1


def ordenaycombinaincluidas(lista,rela, borrar = True, inter=False):
    
    lista.sort(key = lambda x : - len(x.listavar) )

    
    i=0
    while i <len(lista)-1:
        
        j = i+1
        while j < len(lista):
            # print("lista, i, j", len(lista), i, j)
            if set(lista[j].listavar) <= set(lista[i].listavar):
                p = lista[i]
                q = lista[j]
                
                rela.borrarpot(p)
                if borrar:
                    rela.borrarpot(q)
                t = p.combina(q)
                if t.contradict():
                    rela.anula()
                    print("contradicion ")
                    return 
                rela.insertar(t)
                lista[i] = t
                if borrar:
                    lista.remove(q)
                else:
                    j +=1
            else:
                if inter:
                    p = lista[i]
                    q = lista[j]
                    tp = p.mejora(q)
                    tq = q.mejora(p)
                    if tp.contradict() or tq.contradict():
                        rela.anula()
                        print("contradicion ")
                        return

                    rela.borrarpot(p)
                    rela.borrarpot(q)
                    lista[i] = tp
                    lista[j] = tq
                    rela.insertar(tp)
                    rela.insertar(tq)
                

                j+=1
        
        i+=1
    lista.reverse()


def eliminaincluidas(l1,l2):

    borr = []
    for p in l1:
        for j in range(len(l2)):
            q = l2[j]
            if set(p.getvars())<= set(q.getvars()):
                l2[j] = q.combina(p)
                borr.append(p)
                print("no debería ")
                sleep(4)
                
                break
        if p in borr:
            continue
    for p in borr:
        l1.remove(p)

def dist(l1,l2,c):
    s1 = set(l1)
    s2 = set(l2)
    sc = set(c)
    s1.update(sc)
    s2.update(sc)
    su = s1.union(s2)
    return 2**len(su) - 2**len(s1) - 2**len(s2)

def combinasize(lista,pivote):
    c = pivote.getvars()
    i=0
    while i <len(lista)-1:
            
            j = i+1
            while j < len(lista) and i < len(lista):
                if not j==i:
                    p = lista[i]
                    q = lista[j]
                    if dist(p.getvars(),q.getvars(),c)<= 0:
                        p = lista[i]
                        q = lista[j]
                        t = p.combina(q,inplace=False)
                        # if K==0:
                        #     print("No debería")
                        #     sleep(4)
                        
                        lista[i] = t
                        
                        lista.remove(q)
                        j=0
                        
                    else:
                        j+=1
                else:
                    j+=1
            
            i+=1


def combinaincluidas(lista, K=0):
    
    lista.sort(key = lambda x : - len(x.getvars()) )

    
    i=0
    while i <len(lista)-1:
        
        j = i+1
        while j < len(lista):
            # print("lista, i, j", len(lista), i, j)
            if len(set(lista[j].getvars()) - set(lista[i].getvars()))<=K and len(set(lista[j].getvars()).union(set(lista[i].getvars())))<=25:
                p = lista[i]
                q = lista[j]
                t = p.combina(q)
                # if K==0:
                #     print("No debería")
                #     sleep(4)
                
                lista[i] = t
                
                lista.remove(q)
                
            else:
                j+=1
        
        i+=1
    lista.reverse()

def agrupatam(lista):
    
    lista.sort(key = lambda x : - len(x.getvars()) )

    

    i=0
    while i <len(lista)-1:
        
        j = i+1
        while j < len(lista):
            # print("lista, i, j", len(lista), i, j)
            s1 = set(lista[j].listavar)
            s2 = set(lista[i].listavar)
            if s1 <= s2 or ((len(s1) == len(s2) and (len(s1-s2) == 1))):
                p = lista[i]
                q = lista[j]
                
            
                
                t = p.combina(q)
                if t.contradict():
                    print("contradicion ")
                    return 
                
                lista[i] = t
                del lista[j]
                
                

            else:
                j+=1
        
        i+=1
    lista.reverse()

def agrupal(lista, Q):
    listac = lista.copy()
    res = []
    for p in lista:
        # print(p.listavar)
        listat = listac.copy()
        completo = True
        listat.remove(p)
        h = p.copia()
        while listat:
            q = min(listat, key=lambda x: len(set(x.listavar).union(set(h.listavar))))
            if len(set(q.listavar).union(set(h.listavar))) <=Q:
                h.combina(q,inplace=True)
                listat.remove(q)
            else:
                res.append(h)
                completo= False
                break
        if completo:
            res.append(h)
            break
    i=0
    res.sort(key = lambda x : - len(x.listavar) )
    # for x in res:
    #     print (x.listavar)
    #     sleep(3)

    while i <len(res)-1:
        
        j = i+1
        while j < len(res):
            # print("lista, i, j", len(lista), i, j)
            if set(res[j].listavar) <= set(res[i].listavar):
                p = res[i]
                q = res[j]
                t = p.combina(q, inplace=False)
                res[i] = t
                res.remove(q)
                
            else:
                    p = res[i]
                    q = res[j]
                    tp = p.mejora(q)
                    tq = q.mejora(p)
                   

               
                    res[i] = tp
                    res[j] = tq
                  
                

                    j+=1
        
        i+=1


    return res

def createclusters (lista):
    listasets = []
    for cl in lista:
        va = set(map(abs,cl))
        encontrado = False
        for x in listasets:
            if va <= x:
                encontrado = True
                break
            
        if not encontrado:
            listasets.append(va)

    i = 0
    j = 1
    while (i<len(listasets)-1):
        if listasets[i] <= listasets[j]:
            del listasets[i]
            j = i+1
        elif listasets[j] <= listasets[i]:
            del listasets[j]
            if j >= len(listasets):
                i += 1
                j = i+1
        else:
            j += 1
            if j >= len(listasets):
                i += 1
                j = i+1
    listaclaus = []
    for i in range(len(listasets)):
        listaclaus.append([])


    for cl in lista:
        va = set(map(abs,cl))
        for i in range(len(listasets)):
            if va <= listasets[i]:
                listaclaus[i].append(cl)
                break

    return(listasets,listaclaus)



def marginaliza(lista, var, partirin, M=30, Q=1):
    if not lista:
        return (True,[],[])
    if partirin: #EEDM
        partev(lista,var)

   
    res = []
    si = []
    vars = set()
    deter = False
    for p in lista:
        # print(p.listavar)
        if var in p.listavar:

            vars.update(p.listavar)
            si.append(p)
            if not deter:
                deter = p.checkdetermi(var)
                if deter: 
                    nv = set()
                    keyp = p.minimizadep(var,nv)
                    setkey = set(keyp.listavar)
                    # if len(keyp.listavar) < len(p.listavar):
                        # print("minimizo ",len(keyp.listavar) ,  len(p.listavar))
        else:
            # print("warning: variable no en tabla")
            res.append(p)

                                    
        
    if not si:
        return (True,res,[nodoTabla([var])])
    
    exact = True

    if deter:
        print("determinista ")
        vars.discard(var)

        listp = [keyp]
        if len(vars) <= Q:
            # print("global ")
            r = nodoTabla([])
            lc = calculaclusters1(si,keyp,var)
            while si:
                q = si.pop()
                r.combina(q,inplace=True)
            r.borra([var],inplace=True)
            if r.contradict():
                con = nodoTabla([])
                con.anula()
                print("contradiccion")
                return (True,[con],[keyp])
                    

            for h in lc:
                rh = r.borra(list(vars-h)) 
                t = rh.calculaunit()
                if t:
                    print("units ", t)
                        
                if not rh.trivial():
                    res.append(rh)
                        
        else:
            while si:
                q = si.pop() 
                if q == keyp:
                    r = q.borra([var],inplace = False)
                else:
                    if len(setkey.union(set(q.listavar))) < M+1:
                        r = q.combina(keyp,inplace = False, des = False)
                        r.borra([var],inplace = True)

                        if r.contradict():
                            con = nodoTabla([])
                            con.anula()
                            return (True,[con],[])
                        if not r.trivial():
                            t = r.calculaunit()
                            if t:
                                print("unidades ", t)
                            res.append(r)
                    else:
                        print( "no exacto")

                        exact = False

    else:
            si.sort(key = lambda h: - len(h.listavar) )
            print("borrada " , var, "metodo 2, n potenciales", len(si))
            if len(si) >= 30:
                    # print("arupando en tamaño ", len(si))
                    agrupatam(si)
                    # print(len(si))
                    # sleep(3)
            lc = calculaclusters2(si,var)
            vars.discard(var)

            sizes = 0.0
            for xx in lc:
                sizes += 2**len(xx)

            lista = []
            if len(vars) <=Q:
                print ("global total ")
                r = nodoTabla([])
               
                while si:
                    q = si.pop()
                    r.combina(q,inplace=True)
                listp = [r.copia()]
                
                
                
                
                r.borra([var],inplace=True)
                
                
                if r.contradict():
                    con = nodoTabla([])
                    con.anula()
                    return (True,[con],[])

                if not r.trivial():
                        print("entro Units")
                        t = r.calculaunit()
                        print("salgo units")
                        if t:
                            print("unidades ", t)
                        res.append(r)
            
            elif len(vars)<= Q:
                print("global ")

                r = nodoTabla([])
               
                while si:
                    q = si.pop()
                    r.combina(q,inplace=True)
                listp = [r.copia()]
                
                r.borra([var],inplace=True)
                if r.contradict():
                    con = nodoTabla([])
                    con.anula()
                    return (True,[con],[])
                

                for h in lc:
                    rh = r.borra(list(vars-h)) 
                    
                    if not rh.trivial():
                        res.append(rh)
            else:
                print("no global", len(vars), vars)
                # if len(si) >= 30:
                #     print("arupando en tamaño ", len(si))
                #     agrupatam(si)
                #     print(len(si))
                #     sleep(3)
                si2 = si.copy()
                listp = si2
                while si:
                    q = si.pop()
                    # print(q.listavar)

                    for p in si2:
                        if len(set(q.listavar).union(set(p.listavar))) >M+1:
                            print( "no exacto")
                            exact = False
                            return (exact,res,listp)
                        else:
                            r = p.combina(q)
                            r.borra([var], inplace = True)


                            if r.contradict():
                                con = nodoTabla([])
                                con.anula()
                                r = nodoTabla([var])
                                r.tabla[0] = False
                                r.tabla[1] = False
                                return (True, [con],listp)
                    
                            if not r.trivial():
                
                                res.append(r)

                        
            
    print("termina ")        
    return (exact,res,listp)


def marginalizas(lista, var, partirin, M=25):
    if not lista:
        return (True,[],[], set())
    if partirin: #EEDM
        partev(lista,var)

   
    res = []
    si = []
    vars = set()
    units = set()
    deter = False
    lista.sort(key = lambda h:  len(h.listavar) )

    for p in lista:
        if var in p.listavar:

            vars.update(p.listavar)
            si.append(p)
            # print("Potencial p " , p.listavar)
            # x = np.sum(p.tabla)
            # print("Suma ", x, " de ", 2**len(p.listavar))
            if not deter:
                deter = p.checkdetermi(var)
                if deter: 
                    nv = set()
                    keyp = p.minimizadep(var,nv)
                    setkey = set(keyp.listavar)
                    # if len(keyp.listavar) < len(p.listavar):
                        # print("minimizo ",len(keyp.listavar) ,  len(p.listavar))
        else:
            # print("warning: variable no en tabla")
            res.append(p)

                                    
        
    if not si:
        return (True,res,[nodoTabla([var])],set())
    
    exact = True

    if deter:
        # print("determinista ")
        vars.discard(var)

        listp = [keyp]
        for q in si:
            if len(set(q.listavar).union(set(keyp.listavar))) >=M+1:
                            # print( "no exacto")
                            exact = False
                            return (exact,res,listp, set())
    
            
        while si:
            q = si.pop() 
            if q == keyp:
                r = q.borra([var],inplace = False)
            else:
                
                    r = q.combina(keyp,inplace = False, des = False)
                    r.borra([var],inplace = True)

                    if r.contradict():
                            con = nodoTabla([])
                            con.anula()
                            return (True,[con],[],{0})
                    if not r.trivial():
                            # t = r.calculaunit()
                            # if t:
                            #     print("unidades ", t)
                            #     units.update(t)
                            res.append(r)
                    

    else:
            if len(vars) > M:
                return (False, res,[], set())
        
            # print ("global total ")
            r = nodoTabla([])
               
            while si:
                    q = si.pop()
                    r.combina(q,inplace=True)
            listp = [r.copia()]
                
                
                
                
            r.borra([var],inplace=True)
                
                
            if r.contradict():
                    con = nodoTabla([])
                    con.anula()
                    return (True,[con],[],{0})

            if not r.trivial():
                        # print("entro Units")
                        # t = r.calculaunit()
                        # print("salgo units")
                        # if t:
                        #     print("unidades ", t)
                        #     units.update(t)
                        res.append(r)
            
            
            
    # print("termina ")        
    return (exact,res,listp,units)

def topologico(lista):
    orden = []
    padres = dict()
    elegidos = set()
    for x in lista:
        nl = x.copy()
        hijo = nl.pop()
        padres[hijo] = set(nl)
    while padres:
        for x in padres:
            if len(padres[x]- elegidos) == 0:
                break
        elegidos.add(x)
        orden.append(x)
        del padres[x]
    return orden


            
                
                
def calculamethod(lista,var):

        
        
            
            si = []    

            deter = False
            vars = set()

            if len(lista)<=2:
                return 1

            for p in lista:
        
            
                if var in p.listavar:
                        vars.update(p.listavar)
                        si.append(p)
                        if not deter:
                            deter = p.checkdetermi(var)
                            if deter: 
                                return 1
            return 2              
                    
def triangulaconorden(pot,orden):

    n = len(orden)
    clusters = []
    
    child = []
    posvar = dict()
    parent = [-1]*(n+1)

    indexvar = dict()
    for v in orden:
        indexvar[v] = []

    for i in range(n+1):
        child.append(set())
    

    for p in pot.listap:
        con = set(p.listavar)
        for v in con:
            indexvar[v].append(con)
    for v in pot.unit:
        indexvar[abs(v)].append({abs(v)})

    i=0
    for nnodo in orden:
        lista = indexvar[nnodo]
        cluster = set()
        for y in lista:
            cluster.update(y)
        clusters.append(cluster)
        posvar[nnodo] = i
        # print( i, cluster)  #EDM
        i+=1
        clustersin = cluster-{nnodo}

        for y in clustersin:
            indexvar[y] = list(filter( lambda h: nnodo not in h  ,indexvar[y] ))
            indexvar[y].append(clustersin)
           
        




    clusters.append(set())


    for i in range(n):
            con = clusters[i]
            cons = con - {orden[i]}
            if not cons:
                parent[i] = n
                child[n].add(i)
            else:
                pos = min(map(lambda h: posvar[h], cons))
                parent[i] = pos
                child[pos].add(i)



        
            

        
       

            

    # print(orden)
    return (clusters,posvar,child,parent)     

def leeficheroUAI(Archivo):
    lista = list()
    listadatos = list()
    setevid = set()
    archivo=""
    contarClaus=0
    reader=open(Archivo,"r") 
    reader.readline()
    reader.readline()
    reader.readline()
    numFactor = int(reader.readline())
    for i in range(numFactor):
        cadena = reader.readline()
        nodoAdd = nodoTabla([int(i)+1 for i in cadena.split()[1:]])
        lista.append(nodoAdd)
    

    if not 'or_chain' in Archivo and not 'Promedus' in Archivo:
        for l in lista:
            reader.readline()
            lee=int(int(reader.readline())/2)
            lvars=l.listavar
            datos = np.array([])
            for x in range(lee):
                datos=np.append(datos,list(map(float,reader.readline().split())))
            npdatos = datos.reshape((2,)*len(l.listavar))
            l.tabla = npdatos
    elif 'or_chain' in Archivo:
        for l in lista:
            datosb = reader.readline().split()

            while not datosb:
                datosb = reader.readline().split()
               
            del datosb[0]
            datos = np.array(list(map(float,datosb)))

            npdatos = datos.reshape((2,)*len(l.listavar))
            l.tabla = npdatos
    elif 'Promedus' in Archivo:
        reader.readline()
        for l in lista:
            k = int(reader.readline())
            datosb = reader.readline().split()
            datos = np.array(list(map(float,datosb)))

            npdatos = datos.reshape((2,)*len(l.listavar))
            l.tabla = npdatos


      
    
    setevid = leeArchivoEvid(Archivo+".evid")
    return (lista, setevid)


def leeArchivoEvid(Archivo):
    conjEvid=set()
    reader=open(Archivo,"r")

    lines = reader.readlines()
    lunitario = []
    for x in lines:
        lunitario= lunitario + list(map(int,x.strip().split()))
    for x in range(1,len(lunitario),2):
        conjEvid.add((lunitario[x]+1)*(-1 if lunitario[x+1]==0 else 1))
    return conjEvid


def construyeredbay(listap,evi):
    res = pt.problemaTrianFactor()
    res.toriginalfl= listap
    
    res.evid = evi
    return res
