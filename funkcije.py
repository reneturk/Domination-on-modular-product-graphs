import networkx as nx
import random
import math
from itertools import combinations
import pulp
import itertools

def modularni_produkt(G, H):
    """
    Naredi graf GH, kjer so vozlišča kartezični produkt vozlišč grafa G in H,
    povezave pa so narejene v skladu s tremi pravili v definiciji modularnega
    produkta grafov.

    Parametri:
        G (nx.Graph): Vhodni graf G.
        H (nx.Graph): Vhodni graf H.

    Funkcije vrne:
        nx.Graph: Končni graf GH.
    """

    GH = nx.Graph()
    
    # Vozlišča grafa GH so kartezični produkt V(G) x V(H)
    GH_nodes = [(g, h) for g in G.nodes for h in H.nodes]
    GH.add_nodes_from(GH_nodes)
    
    for g1, h1 in GH_nodes:
        for g2, h2 in GH_nodes:            
            # Tri pravila za preverjanje modularnega produkta
            if (g1 == g2 and (h1, h2) in H.edges) or ((g1, g2) in G.edges and h1 == h2):
                GH.add_edge((g1, h1), (g2, h2))
            elif (g1, g2) in G.edges and (h1, h2) in H.edges:
                GH.add_edge((g1, h1), (g2, h2))
            elif (g1 != g2 and h1 != h2) and (g1, g2) not in G.edges and (h1, h2) not in H.edges:
                GH.add_edge((g1, h1), (g2, h2))
    
    return GH


def dominacijsko_stevilo(G: nx.Graph) -> int:
    """
    Najde dominacijsko število grafa s pomočjo linearnega programiranja.

    Parametri:
        G (nx.Graph): Vhodni graf G.

    Funkcija vrne dominacijsko število grafa.
    """
    # Naredimo linearni program
    lp = pulp.LpProblem("DominacijskoStevilo", pulp.LpMinimize)

    # Za vsako vozlišče definiramo odločitveno binarno spremenljivko x (bodisi enaka 1 ali 0)
    x = {vozlisce: pulp.LpVariable(f"x_{vozlisce}", cat="Binary") for vozlisce in G.nodes}

    # Hočemo minimizirati vsoto odločitvenih spremenljivk
    lp += pulp.lpSum(x.values())

    # Pogoji: Vsako vozlišče mora biti dominirano
    for vozlisce in G.nodes:
        # Vozlišče je dominirano, če je element dominacijske množice ali če je
        # njegov sosed element dominacijske množice
        lp += pulp.lpSum(x[sosed] for sosed in G.neighbors(vozlisce)) + x[vozlisce] >= 1

    # Rešimo linearni program
    lp.solve()

    # Program vrne dominacijsko število (minimalna moč dominacijske množice grafa)
    return int(pulp.value(lp.objective))


def zmanjsaj_premer_na_2(G):
    """
    Modificiramo graf, da reduciramo njegov premer na 2, ki doda povezave naključno.
    Deluje tudi za nepovezane grafe

    Parametri:
        G (nx.Graph): Vhodni graf G.

    Funkcija vrne:
        nx.Graph: Modificiran graf s premerom zreduciranim na 2.
    """
    # Dokler graf ni povezan, dodajamo povezave (sem imel probleme s to funkcijo, če graf ni bil povezan)
    while not nx.is_connected(G):
        # Poiščemo komponente (vsaka komponenta je množica vozlišč)
        komponente = list(nx.connected_components(G))
        
        # Naključno izberemo dve različni komponenti
        c1, c2 = random.sample(komponente, 2)
        
        # Naključno izberemo eno vozlišče iz vsake komponente in jih povežemo
        v1 = random.choice(list(c1))
        v2 = random.choice(list(c2))
        G.add_edge(v1, v2)

    while nx.diameter(G) > 2:
        # Najdemo dve vozlišči na maksimalni razdalji
        u, v = max(
            ((a, b) for a in G.nodes for b in G.nodes if a != b),
            key=lambda pair: nx.shortest_path_length(G, source=pair[0], target=pair[1])
        )

        # Najdemo najkrajšo pot med tema dvema vozliščema
        najkrajsa_pot = nx.shortest_path(G, source=u, target=v)

        # Če je dolžina poti večja od 3, naključno izberemo dve vozlišči iz nje in ju povežemo
        if len(najkrajsa_pot) > 3:
            i, j = sorted(random.sample(range(len(najkrajsa_pot)), 2))  # Naključno izberemo dve vozlišči
            G.add_edge(najkrajsa_pot[i], najkrajsa_pot[j])

    return G

def stohasticno_iskanje_grafa(n, max_iter=1000):
    """
    Stohastično iskanje grafa G, ki ustreza naslednjemju pogoju:
        \gamma(G ⊕ G) \geq \gamma(G) + 2,
    kjer je ⊕ znak za modularni produkt grafov.

    Parametri:
        n (int): Število vozlišč grafa G.
        max_iter (int): Maksimalno število iteracij.

    Funkcija vrne:
        networkx.Graph: Graf, ki ustreza pogoju, če ga funkcija dobi.
    """
    dobljeni_graf = None
    for _ in range(max_iter):
        # Generiramo naključen graf z n vozlišči in naključnim številom povezav.
        num_edges = random.randint(n-1, n * (n - 1) // 2)
        G = nx.gnm_random_graph(n, num_edges)

        # Poskrbimo, da bo graf G povezan
        if not nx.is_connected(G):
            continue  # Preskočimo to iteracijo, če graf G ni povezan
        
        # Zmanjšamo premer grafa na 2
        G = zmanjsaj_premer_na_2(G)

        # Izračunajmo dominacijska števila grafa G in GG
        gamma_G = dominacijsko_stevilo(G)
        GG = modularni_produkt(G, G)
        gamma_GG = dominacijsko_stevilo(GG)
        # Preverimo če za G velja pogoj, ki ga iščemo
        if gamma_GG >= gamma_G + 2:
            dobljeni_graf = G
            break

    return dobljeni_graf

# Poskusim še narediti funkcijo, ki naredi graf na n vozliščih tako, da
# naključno dodaja povezave, dokler graf ni povezan
def konstruiraj_povezan_graf(n):
    G = nx.gnm_random_graph(n, 0)  # Začnemo z n vozlišči in brez povezav
    
    # Dokler graf ni povezan, dodajamo povezave
    while not nx.is_connected(G):
        # Poiščemo komponente (vsaka komponenta je množica vozlišč)
        komponente = list(nx.connected_components(G))
        
        # Naključno izberemo dve različni komponenti
        c1, c2 = random.sample(komponente, 2)
        
        # Naključno izberemo eno vozlišče iz vsake komponente in jih povežemo
        v1 = random.choice(list(c1))
        v2 = random.choice(list(c2))
        G.add_edge(v1, v2)
    
    return G

# Funkcija, ki za razliko od prejšnje, ne konstruira grafa z naključnim številom povezav in pogleda, če je ta povezan,
# ampak uporabi funkcijo konstruiraj_povezan_graf, da naključno dodaja povezave, dokler graf ni povezan.
def stohasticno_iskanje_grafa_2(n, max_iter=1000):
    ustrezni_grafi = []
    for _ in range(max_iter):
        G = konstruiraj_povezan_graf(n)
        
        # Zmanjšamo premer grafa na 2
        G = zmanjsaj_premer_na_2(G)

        # Izračunajmo dominacijska števila grafa G in GG
        gamma_G = dominacijsko_stevilo(G)
        GG = modularni_produkt(G, G)
        gamma_GG = dominacijsko_stevilo(GG)
        # Preverimo če za G velja pogoj, ki ga iščemo
        if gamma_GG >= gamma_G + 2:
            ustrezni_grafi.append(G)

    return ustrezni_grafi

# Bom odstranu nekaj povezav naključno (dobesedno, kot to piše v navodilih od projekta),
# namesto da vsakič generiram nov graf
def stohasticno_iskanje_grafa_3(n, max_iter = 1000):
    ustrezni_grafi = []
    max_inner_iter = 100  # Omejitev notranjih iteracij
    for _ in range(max_iter//max_inner_iter):
        G = konstruiraj_povezan_graf(n)
        inner_iter = 0
        while inner_iter < max_inner_iter:
            # Zmanjšamo premer grafa na 2
            G = zmanjsaj_premer_na_2(G)

            # Izračunajmo dominacijska števila grafa G in GG
            gamma_G = dominacijsko_stevilo(G)
            GG = modularni_produkt(G, G)
            gamma_GG = dominacijsko_stevilo(GG)
            
            # Preverimo, če za G velja pogoj, ki ga iščemo
            if gamma_GG >= gamma_G + 2:
                ustrezni_grafi.append(G)
                break
            else:
                # Naključno odstranimo nekaj povezav
                povezave = list(G.edges)
                st_odstrani = random.randint(1, max(1, len(povezave) // 2))
                odstrani_povezave = random.sample(povezave, st_odstrani)
                G.remove_edges_from(odstrani_povezave)
            
            inner_iter += 1
    
    return ustrezni_grafi


# Funkcija, ki imajo a na koncu sem napisal za potrebe risanja prikaza (glej poročilo)

def stohasticno_iskanje_grafa_1a(n, max_iter=1000):
    rezultati = []
    for _ in range(max_iter):
        # Generiramo naključen graf z n vozlišči in naključnim številom povezav.
        num_edges = random.randint(n-1, n * (n - 1) // 2)
        G = nx.gnm_random_graph(n, num_edges)

        # Poskrbimo, da bo graf G povezan
        if not nx.is_connected(G):
            continue  # Preskočimo to iteracijo, če graf G ni povezan
        
        # Zmanjšamo premer grafa na 2
        G = zmanjsaj_premer_na_2(G)

        # Izračunajmo dominacijska števila grafa G in GG
        gamma_G = dominacijsko_stevilo(G)
        GG = modularni_produkt(G, G)
        gamma_GG = dominacijsko_stevilo(GG)
        rezultati.append((gamma_G, gamma_GG))
    return rezultati


def stohasticno_iskanje_grafa_2a(n, max_iter=1000):
    rezultati = []
    for _ in range(max_iter):
        G = konstruiraj_povezan_graf(n)
        
        # Zmanjšamo premer grafa na 2
        G = zmanjsaj_premer_na_2(G)

        # Izračunajmo dominacijska števila grafa G in GG
        gamma_G = dominacijsko_stevilo(G)
        GG = modularni_produkt(G, G)
        gamma_GG = dominacijsko_stevilo(GG)
        rezultati.append((gamma_G, gamma_GG))
    return rezultati


def stohasticno_iskanje_grafa_3a(n, max_iter = 1000):
    ustrezni_grafi = []
    max_inner_iter = 100  # Omejitev notranjih iteracij
    rezultati = []
    for _ in range(max_iter//max_inner_iter):
        G = konstruiraj_povezan_graf(n)
        inner_iter = 0
        while inner_iter < max_inner_iter:
            # Zmanjšamo premer grafa na 2
            G = zmanjsaj_premer_na_2(G)

            # Izračunajmo dominacijska števila grafa G in GG
            gamma_G = dominacijsko_stevilo(G)
            GG = modularni_produkt(G, G)
            gamma_GG = dominacijsko_stevilo(GG)
            rezultati.append((gamma_G, gamma_GG))
            # Preverimo, če za G velja pogoj, ki ga iščemo
            if gamma_GG >= gamma_G + 2:
                ustrezni_grafi.append(G)
                break
            else:
                # Naključno odstranimo nekaj povezav
                povezave = list(G.edges)
                st_odstrani = random.randint(1, max(1, len(povezave) // 2))
                odstrani_povezave = random.sample(povezave, st_odstrani)
                G.remove_edges_from(odstrani_povezave)
            
            inner_iter += 1
    
    return rezultati


def generiraj_vse_povezane_grafe(n):
    """
    Generira vse povezane grafe na n vozliščih.
    
    Parametri:
        n (int): Število vozlišč.
    
    Vrne:
        list[nx.Graph]: Seznam vseh povezanih grafov na n vozliščih.
    """
    vozlisca = list(range(n))
    # Naredimo seznam vseh možnih povezav v polnem grafu
    vse_mozne_povezave = list(itertools.combinations(vozlisca, 2))
    povezani_grafi = []
    
    # Iteriramo čez vse možne podmnožice povezav, ki imajo vsaj n-1 povezav
    for k in range(n - 1, len(vse_mozne_povezave) + 1):
        for povezave in itertools.combinations(vse_mozne_povezave, k):
            G = nx.Graph()
            G.add_nodes_from(vozlisca)
            G.add_edges_from(povezave)
            
            if nx.is_connected(G):  # Preverimo povezanost
                povezani_grafi.append(G)
    
    return povezani_grafi

from networkx.algorithms.isomorphism import GraphMatcher

def vrni_neizomorfne_grafe(sez_grafov):
    koncni_grafi = []

    for G in sez_grafov:
        if not any(GraphMatcher(G,H).is_isomorphic() for H in koncni_grafi):
            koncni_grafi.append(G)
    return koncni_grafi

import itertools
import networkx as nx

def generiraj_milijon_povezanih_grafov(n):
    """
    Generira največ milijon povezanih grafov na n vozliščih.
    
    Parametri:
        n (int): Število vozlišč.
    
    Vrne:
        list[nx.Graph]: Seznam do največ milijon povezanih grafov na n vozliščih.
    """
    vozlisca = list(range(n))
    vse_mozne_povezave = list(itertools.combinations(vozlisca, 2))
    povezani_grafi = []
    
    # Iteriramo čez vse možne podmnožice povezav, ki imajo vsaj n-1 povezav
    for k in range(n - 1, len(vse_mozne_povezave) + 1):
        for povezave in itertools.combinations(vse_mozne_povezave, k):
            G = nx.Graph()
            G.add_nodes_from(vozlisca)
            G.add_edges_from(povezave)
            
            if nx.is_connected(G):  # Preverimo povezanost
                povezani_grafi.append(G)
                
                # Če dosežemo milijon grafov, prekinemo zanko
                if len(povezani_grafi) >= 1000000:
                    return povezani_grafi
    
    return povezani_grafi
