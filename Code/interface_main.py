from Code.aima.utils import expr
from aima.logic import *
import nltk
import speech_recognition as sr
from gtts import gTTS
import keyboard
from pydub import AudioSegment
from pydub.playback import play
import constants
import os

# Liste des fichiers de grammaire en ordre pour trouver le bon.
grammars = [
    'arme_piece',
    'personne_piece_heure',
    'personne_morte_heure',
    'personne_vivant',
    'personne_piece',
    'personne_morte',
    'personne_marque'
]


class CrimeInference:
    def __init__(self):
        self.weapons = ["Corde", "Fusil", "Couteau", "Marteau", "Baton", "CléÉcrous"]
        self.rooms = ["Cave", "Garage", "Balcon", "Bureau", "Cuisine", "Salon"]
        self.persons = ["Mustard", "Peacock", "Scarlet", "Plum", "White", "Olive"]

        # Liste de clauses (faits) qui seront stockées dans la base de connaissance.
        self.clauses = []

        self.base_clauses()
        self.initialize_KB()
        self.inference_rules()

        # Base de connaissances (First-order logic - FOL)
        self.crime_kb = FolKB(self.clauses)

    # Déclaration dans la logique du premier ordre
    def base_clauses(self):
        # Le paramètre est une arme
        self.arme_clause = 'Arme({})'

        # Le paramètre est une pièce
        self.piece_clause = 'Piece({})'

        # Le paramètre est une persone
        self.personne_clause = 'Personne({})'

        # paramètre 1 : arme; paramètre 2 : pièce
        # p.ex.: Le couteau se trouve dans la cuisine
        self.weapon_room_clause = 'Arme_Piece({},{})'

        # paramètre 1 : personne; paramètre 2 : pièce; paramètre 3 : heure
        # p.ex.: Mustart était dans la cuisine à 11h00
        self.person_room_hour_clause = 'Personne_Piece_Heure({}, {}, {})'

        # paramètre 1 : personne; paramètre 2 : piece
        # p.ex.: Mustard se trouve dans la cuisine
        self.person_room_clause = 'Personne_Piece({}, {})'

        # paramète 1 : personne
        # p. ex.: Mustard est mort
        self.dead_clause = 'EstMort({})'

        # paramète 1 : personne
        # p. ex.: Mustard est vivant
        self.alive_clause = 'EstVivant({})'

        # paramètre 1 : personne
        # p. ex.: Mustard est la victime
        self.victim_clause = 'Victime({})'

        # paramètre 1 : personne
        # p. ex.: Mustard a des marques au cou; Peacock a un trou a la tete
        self.body_mark_clause = 'Marque({})'

        # paramètre 1: personne; paramètre 2: personne
        self.person_different_clause = 'PersonneDifferente({},{})'

        # paramètre 1 : piece; paramètre 2 : piece
        self.room_different_clause = 'PieceDifferente({},{})'

        # paramètre 1 : piece; paramètre 2 : piece
        self.weapon_different_clause = 'ArmeDifferente({},{})'

        # paramètre 1 : heure
        self.crime_hour_clause = 'HeureCrime({})'

        # paramètre 1 : heure
        self.crime_hour_plus_one_clause = 'UneHeureApresCrime({})'

    def initialize_KB(self):
        # Clause pour differencier les personnes
        for i in range(len(self.persons)):
            for j in range(len(self.persons)):
                if i != j:
                    # Moutarde est different de Scarlet = PersonneDifferente(Moutarde, Scarlet)
                    self.clauses.append(expr(self.person_different_clause.format(self.persons[i], self.persons[j])))

        # Clause pour differencier les pièces
        for i in range(len(self.rooms)):
            for j in range(len(self.rooms)):
                if i != j:
                    # Le bureau est different de la cuisine = PieceDifferente(Bureau, Cuisine)
                    self.clauses.append(expr(self.room_different_clause.format(self.rooms[i], self.rooms[j])))

        # Clause pour differencier les armes
        for i in range(len(self.weapons)):
            for j in range(len(self.weapons)):
                if i != j:
                    # Le couteau est different de la corde = ArmeDifferente(Couteau, Corde)
                    self.clauses.append(expr(self.weapon_different_clause.format(self.weapons[i], self.weapons[j])))

        # Initialiser KB sur Armes, Pieces, Personnes
        for weapon in self.weapons:
            # Le couteau est une arme = Arme(Couteau)
            self.clauses.append(expr(self.arme_clause.format(weapon)))

        for room in self.rooms:
            # La cuisine est une pièce = Piece(Cuisine)
            self.clauses.append(expr(self.piece_clause.format(room)))

        for person in self.persons:
            # Mustar est une personne = Personne(Mustard)
            self.clauses.append(expr(self.personne_clause.format(person)))

    # Expressions dans la logique du premier ordre permettant de déduire les caractéristiques du meurtre.
    def inference_rules(self):

        # Determine la piece du crime.
        self.clauses.append(expr('EstMort(x) & Personne_Piece(x, y) ==> PieceCrime(y)'))

        # Determine l'arme du crime si arme est dans la pièce du crime.
        self.clauses.append(expr('PieceCrime(x) & Arme(y) & Piece_Arme(y, x) ==> ArmeCrime(y)'))

        ############################# Marques ##############################
        # Determine l'arme du crime si les marques sont respectives a une arme.
        # Une marque au coup est faite par une corde.
        self.clauses.append(expr("EstMort(x) & Marque(x,Marque) ==> ArmeCrime(Corde)"))
        # Un trou dans le corps est fait par un fusil.
        self.clauses.append(expr("EstMort(x) & Marque(x,Trou) ==> ArmeCrime(Fusil)"))
        # Une enflure dans le corps est faite par une clé à écrous.
        self.clauses.append(expr("EstMort(x) & Marque(x,Enflure) ==> ArmeCrime(CléÉcrous)"))
        # Une fracture  dans le corps est faite par un baton.
        self.clauses.append(expr("EstMort(x) & Marque(x,Fracture) ==> ArmeCrime(Baton)"))
        # Une brisure dans le corps est faite par un marteau.
        self.clauses.append(expr("EstMort(x) & Marque(x,Brisure) ==> ArmeCrime(Marteau)"))
        # Une coupure dans le corps est fait par un couteau.
        self.clauses.append(expr("EstMort(x) & Marque(x,Coupure) ==> ArmeCrime(Couteau)"))
        ####################################################################

        # Si la personne est morte alors elle est la victime et ce n'est pas un suicide.
        self.clauses.append(expr('EstMort(x) ==> Victime(x)'))

        # Si la personne est morte alors elle est innocente et ce n'est pas un suicide.
        self.clauses.append(expr('EstMort(x) ==> Innocent(x)'))

        # Si la personne était dans une salle différente que celle du crime, il est innocent.
        self.clauses.append(expr(
            'HeureCrime(h) & Personne_Piece_Heure(p, r1, h) & PieceCrime(r2) & PieceDifferente(r1, r2) ==> Innocent(p)'
        ))

        # Si la personne n'est pas morte, alors elle est vivante.
        self.clauses.append(expr(
            'Personne_Piece(p1, r) & EstMort(p2) & PersonneDifferente(p1, p2) ==> EstVivant(p1)'
        ))

        # Si la personne n'est le meurtrier, alors elle est innocente.
        self.clauses.append(expr(
            'EstVivant(p1) & Suspect(p2) & PersonneDifferente(p1, p2) ==> Innocent(p1)'
        ))

        # Si la personne est vivante et était dans une pièce
        # qui ne contient pas l'arme du crime, alors elle est innocente.
        self.clauses.append(expr(
            'EstVivant(p) & UneHeureApresCrime(h1) & Personne_Piece_Heure(p,r2,h1) & PieceCrime(r1)'
            ' & PieceDifferente(r1,r2) & ArmeCrime(a1) & Arme_Piece(a2,r2) & ArmeDifferente(a1,a2) ==> Innocent(p)'))

        # Si la personne se trouvait dans une piece qui contient l'arme
        # qui a tué la victime une heure après le meurtre alors elle est suspecte.
        self.clauses.append(expr(
            'EstVivant(p) & UneHeureApresCrime(h1) & Personne_Piece_Heure(p,r2,h1) & PieceCrime(r1)'
            ' & PieceDifferente(r1,r2) & ArmeCrime(a) & Arme_Piece(a,r2) ==> Suspect(p)'))

    # Ajouter des clauses, c'est-à-dire des faits, à la base de connaissances
    def add_clause(self, clause_string):
        self.crime_kb.tell(expr(clause_string))

    # Demander à la base de connaissances qui est la victime
    def get_victim(self):
        result = self.crime_kb.ask(expr('Victime(x)'))
        if not result:
            return False
        else:
            return result[x]

    # Demander à la base de connaissances la pièce du meurtre
    def get_crime_room(self):
        result = self.crime_kb.ask(expr('PieceCrime(x)'))
        if not result:
            return False
        else:
            return result[x]

    # Demander à la base de connaissances l'arme du meurtrier
    def get_crime_weapon(self):
        result = self.crime_kb.ask(expr('ArmeCrime(x)'))
        if not result:
            return result
        else:
            return result[x]

    # Demander à la base de connaissances l'heure du meurtre
    def get_crime_hour(self):
        result = self.crime_kb.ask(expr('HeureCrime(x)'))
        if not result:
            return result
        else:
            return result[x]

    # Demander à la base de connaissances l'heure du meurtre + 1
    def get_crime_hour_plus_one(self):
        result = self.crime_kb.ask(expr('UneHeureApresCrime(x)'))
        if not result:
            return result
        else:
            return result[x]

    # Demander à la base de connaissances le suspect
    def get_suspect(self):
        result = self.crime_kb.ask(expr('Suspect(x)'))
        if not result:
            return result
        else:
            return result[x]

    # Demander à la base de connaissances la liste d'innocents
    def get_innocent(self):
        result = list(fol_bc_ask(self.crime_kb, expr('Innocent(x)')))
        res = []

        for elt in result:
            if not res.__contains__(elt[x]):
                res.append(elt[x])
        return res


# Référence : https://realpython.com/python-speech-recognition/
class SpeechRecognition:
    recognizer = sr.Recognizer()
    microphone = sr.Microphone()

    def recognize_speech_from_mic(self):
        # check that recognizer and microphone arguments are appropriate type
        if not isinstance(self.recognizer, sr.Recognizer):
            raise TypeError("`recognizer` must be `Recognizer` instance")

        if not isinstance(self.microphone, sr.Microphone):
            raise TypeError("`microphone` must be `Microphone` instance")

        self.recognizer.pause_threshold = 2

        # microphone sensitivity.
        with self.microphone as source:
            self.recognizer.adjust_for_ambient_noise(source)
            audio = self.recognizer.listen(source)

        # set up the response object
        response = {
            "success": True,
            "error": None,
            "transcription": None
        }

        # try recognizing the speech in the recording
        # if a RequestError or UnknownValueError exception is caught,
        #     update the response object accordingly
        try:
            response["transcription"] = self.recognizer.recognize_google(audio, language='fr-FR')
        except sr.RequestError:
            # API was unreachable or unresponsive
            response["success"] = False
            response["error"] = "API unavailable"
        except sr.UnknownValueError:
            # speech was unintelligible
            response["error"] = "Unable to recognize speech"

        return response

    def listen_to_mic(self):
        print(constants.waiting_audi_response)
        speech = self.recognize_speech_from_mic()

        # if there was an error, stop
        if speech["error"]:
            print("ERROR: {}".format(speech["error"]))
        else:

            # Enregistre la réponse vocale en fait.
            fact = speech["transcription"]
            print("Message reçu !")
            return fact



# Méthode qui translate les phrases en faits.
def translate_string_to_fact(facts):
    found = False

    for grammar in grammars:
        try:
            agent.add_clause(to_fol(facts, 'grammars/' + grammar + '.fcfg'))
            found = True

            hour = agent.get_crime_hour()
            if hour:
                agent.add_clause('UneHeureApresCrime({})'.format(hour + 1))

            break
        except:
            pass

    if not found:
        print("Fact invalid:", facts)


def open_read_file(nom_fichier):
    try:
        file = open(nom_fichier + ".txt", "r", encoding='utf-8')
        for line in file:
            line = line.rstrip('\n')
            if line.startswith('#') or line == '':
                continue
            # Lecture des faits de bases.
            facts = [line]
            translate_string_to_fact(facts)
        file.close()
    except:
        print(constants.file_error)
    finally:
        file.close()


class TextRecognition:

    def get_input_from_keyboard(self):
        print('Tapez votre réponse :')
        str = input()
        print("D'accord!")
        return str


class SpeechToText:
    # Code source tiré de https://ena.etsmtl.ca/mod/resource/view.php?id=696807
    def text_to_wav(self, text):
        # Language in which you want to convert
        language = 'fr'

        myobj = gTTS(text=text, lang=language, slow=False)
        myobj.save("audio.mp3")
        play(AudioSegment.from_mp3("audio.mp3"))

        # supprimé après chaque fois.
        os.remove("audio.mp3")


def get_room_names(rooms_dict):
    rooms = []
    counter = 1
    for _ in rooms_dict.keys():
        counter = str(counter)
        name = rooms_dict[counter]["person_name"]
        counter = int(counter)
        counter = counter + 1
        rooms.append(name)
    return rooms


# Méthode qui détermine si une pièce a été visité ou non.
def get_room_status(rooms_dict):
    status = []
    counter = 1
    for _ in rooms_dict.keys():
        counter = str(counter)
        name = rooms_dict[counter]["status"]
        counter = int(counter)
        counter = counter + 1
        status.append(name)
    return status


# Méthode qui retourne le numéro de la pièce.
def get_room_number(rooms_dict, room_id):
    counter = 1
    name = ""
    for _ in rooms_dict.keys():
        if counter == room_id:
            room_id = str(room_id)
            name = rooms_dict[room_id]["person_name"]
            break
        else:
            while counter != room_id:
                counter = counter + 1
            room_id = str(room_id)
            name = rooms_dict[room_id]["person_name"]
            break

    return name


# Méthode qui détermine le nom de la pièce.
def get_room_name(rooms_dict, room_id):
    counter = 1
    name = ""
    for _ in rooms_dict.keys():
        if counter == room_id:
            room_id = str(room_id)
            name = rooms_dict[room_id]["person_name"]
            break
        else:
            while counter != room_id:
                counter = counter + 1
            room_id = str(room_id)
            name = rooms_dict[room_id]["person_name"]
            break

    return name

# Méthode qui imprime les pièces avec leur status.
def print_rooms(rooms_dict):
    rooms = get_room_names(rooms_dict)
    status = get_room_status(rooms_dict)
    print("######################## Rooms ###############################")
    print("1:      " + rooms[0] + "(" + status[0] + ")   #################  4: " + rooms[3] + "(" + status[3] + ")")
    print("###### |     | #################################### |     | ")
    print("2:      " + rooms[1] + "(" + status[1] + ") +++++++++++++++++  5: " + rooms[4] + "(" + status[4] + ")")
    print("###### |     | #################################### |     | ")
    print("3:      " + rooms[2] + "(" + status[2] + ") +++++++++++++++++  6: " + rooms[5] + "(" + status[5] + ")")
    print("######################## Rooms ###############################")


# Méthode qui détermine si la pièce était visité ou non.
def is_visited(rooms_dict, room_id):
    counter = 1
    status = ""
    for _ in rooms_dict.keys():
        if counter == room_id:
            room_id = str(room_id)
            status = rooms_dict[room_id]["status"]
            break
        else:
            while counter != room_id:
                counter = counter + 1

        room_id = str(room_id)
        status = rooms_dict[room_id]["status"]
        break
    if status == "visited":
        return bool(True)
    else:
        return bool(False)


def print_question(question):
    speechToText.text_to_wav(question)
    print(question)


def print_fact(facts):
    speechToText.text_to_wav(facts)
    print(facts)


# Méthode qui enregistre la direction du l'utilisateur.
def press_key(direction):
    while True:
        if direction == "down" and keyboard.is_pressed('down'):
            correct_key = bool(True)
            break
        if direction == "up" and keyboard.is_pressed('up'):
            correct_key = bool(True)
            break
        if direction == "right" and keyboard.is_pressed('right'):
            correct_key = bool(True)
            break
        if direction == "left" and keyboard.is_pressed('left'):
            correct_key = bool(True)
            break
    return correct_key


def get_audio_or_text_choice():
    print('Appuyez soit la lettre s pour le microphone ou la lettre t pour le clavier.')
    answer = input()

    while answer != 't' and answer != 's':
        print("Il faut peser 't' pour écrire et 's' pour audio vocale")
        answer = get_audio_or_text_choice()
    return answer


def get_info_from_user():
    key2 = get_audio_or_text_choice()
    if key2 == 's':
        return sR.listen_to_mic()

    elif key2 == 't':
        return tR.get_input_from_keyboard()


def ask_crime_hour(victime):
    print_question("Quel est l'heure du meurtre ?")
    temps = get_info_from_user()
    if temps:
        print("Nouveau faits")
        fact = ['%s est morte à %sh' % (victime, temps)]
        agent.add_clause(to_fol(fact, 'grammars/personne_morte_heure.fcfg'))
        print_fact('La victime: %s est morte à %sh' % (victime, temps))
        hour = agent.get_crime_hour()
        if hour:
            agent.add_clause('UneHeureApresCrime({})'.format(hour + 1))


# Méthode qui retourne soit oui ou non de l'utilisateur.
def yes_or_no_answer():
    print(constants.yes_or_no_question)
    answer = input()

    while answer != '2' and answer != '1':
        print("Il faut peser le 0 si c'est faux et 1 si c'est vrai.")
        answer = yes_or_no_answer()
    return answer


# Methode qui determine si la victime est connu ou non
def get_victime():
    if not agent.get_victim():
        print_question(constants.victim_question)
        victime = get_info_from_user()
        if victime:
            fact = ['%s est mort' % (victime)]
            agent.add_clause(to_fol(fact, 'grammars/personne_morte.fcfg'))
            print("Nouveau faits: ")
            print_fact('%s est morte' % (victime))
            print()
            ask_crime_hour(victime)

    if agent.get_victim():
        if not agent.get_crime_hour():
            ask_crime_hour(victime)


# Méthode qui détermine si il y ou non une arme dans la pièce.
def get_weapon_in_room(room_dict, room_id):
    print()
    print_question(constants.weapon_question)
    answer = yes_or_no_answer()
    if answer == constants.oui:
        data = get_info_from_user()
        if data != "no data":
            room = get_room_name(room_dict, room_id)
            fact = ['Le %s est dans le %s' % (data, room)]
            agent.add_clause(to_fol(fact, 'grammars/arme_piece.fcfg'))
            print("Nouveau faits")
            print_fact('Le %s est dans la pièce: %s' % (data, room))

    else:
        print('Aucune arme détectée dans la pièce !')

# Méthode qui détermine quelle est personne dans la pièce actuelle.
def get_person_in_room(room):
    print_question(constants.person_room_current_time_question)
    answer = yes_or_no_answer()
    if answer == constants.oui:
        people = get_info_from_user()
        if people:
            people = people.split()
            for name in people:

                # Ajouter les personnes non victimes comme vivant.
                if aima.utils.Expr(name) != agent.get_victim():
                    fact = ['%s est dans le %s' % (name, room)]
                    agent.add_clause(to_fol(fact, 'grammars/personne_piece.fcfg'))

                    fact = ['%s est vivant' % (name)]
                    agent.add_clause(to_fol(fact, 'grammars/personne_vivant.fcfg'))
                    get_person_in_room_one_hour_after_crime(name)

                # Si la personne est la victime, il faut demander sa blessure.
                else:
                    fact = ["%s est dans la %s" % (name, room)]
                    agent.add_clause(to_fol(fact, 'grammars/personne_piece.fcfg'))
                    print_question("Quelle type de blessure a soufert la victime?")
                    marque = get_info_from_user()
                    if marque:
                        agent.add_clause(to_fol([marque], 'grammars/personne_marque.fcfg'))
                        print_fact(marque)
    else:
        print('Aucune personne détectée dans la pièce.')

# Méthode qui détermine la pièce de la personne 1 heure après le meurtre.
def get_person_in_room_one_hour_after_crime(person_name):
    print_question("Dans quelle pièce était %s une heure après le meurtre ?" % (person_name))
    uneHeureApres = agent.get_crime_hour() + 1
    crimeRoom = get_info_from_user()
    if crimeRoom != "no data":
        fact = ["%s était dans le %s à %sh" % (person_name, crimeRoom, str(uneHeureApres))]
        agent.add_clause(to_fol(fact, 'grammars/personne_piece_heure.fcfg'))
        print("Nouveau faits: ")
        print_fact(
            "%s était dans la pièce: %s à %sh" % (person_name, crimeRoom, str(uneHeureApres)))


# Méthode qui entrepend les nouveaux faits.
def get_new_facts(room_dict, room_id):

    # Détermine la victime.
    get_victime()

    # Détermine l'arme dans la pièce.
    get_weapon_in_room(room_dict, room_id)

    print()

    # Détermine la personne dans la pièce.
    get_person_in_room(get_room_name(room_dict, room_id))




# Méthode qui enregistre les pièces visitées.
def set_visited(rooms_dict, room_id):
    counter = 1
    for _ in rooms_dict.keys():
        if counter == room_id:
            room_id = str(room_id)
            rooms_dict[room_id]["status"] = "visited"
            break
        else:
            while counter != room_id:
                counter = counter + 1

        room_id = str(room_id)
        rooms_dict[room_id]["status"] = "visited"
        break


# Méthode qui se renseinge sur les faits de la pièce correspondante.
def set_fact_from_room(rooms_dict, room_id):
    print(constants.room_assertion + get_room_name(rooms_dict, room_id))
    if is_visited(rooms_dict, room_id) == bool(False):
        get_new_facts(rooms_dict, room_id)
        set_visited(rooms_dict, room_id)
    else:
        print("Piàce déjà visitée")


# Méthode qui permet à l'agent de se déplacer.
def visit_rooms(rooms_dict, room_id):
    print("Appuyer sur une flèche de direction")
    while True:
        if keyboard.is_pressed('down'):
            room_id = 6
            print("Vous allez à la dernière pièce.")
            set_fact_from_room(rooms_dict, room_id)
            set_visited(rooms_dict, room_id)
            break

        if keyboard.is_pressed('up'):
            room_id = 1
            print("Vous allez à la pièce débutante.")
            set_fact_from_room(rooms_dict, room_id)
            set_visited(rooms_dict, room_id)
            break

        if keyboard.is_pressed('right'):
            room_id = room_id + 1
            print("Vous allez à la prochaine pièce")
            set_fact_from_room(rooms_dict, room_id)
            set_visited(rooms_dict, room_id)
            break

        if keyboard.is_pressed('left'):
            room_id = room_id - 1
            print("Vous allez à la piàce antécédante")
            set_fact_from_room(rooms_dict, room_id)
            set_visited(rooms_dict, room_id)
            break
    return room_id


def init_rooms():
    cave = {
        "person_name": "cave",
        "status": "not visited",
        "room_id": "1"
    }
    garage = {
        "person_name": "garage",
        "status": "not visited",
        "room_id": "2"
    }
    balcon = {
        "person_name": "balcon",
        "status": "not visited",
        "room_id": "3"
    }
    bureau = {
        "person_name": "bureau",
        "status": "not visited",
        "room_id": "4"
    }
    cuisine = {
        "person_name": "cuisine",
        "status": "not visited",
        "room_id": "5"
    }
    salon = {
        "person_name": "salon",
        "status": "not visited",
        "room_id": "6"
    }
    rooms_dict = {
        "1": cave,
        "2": garage,
        "3": balcon,
        "4": bureau,
        "5": cuisine,
        "6": salon,
    }
    return rooms_dict


def main(agent):
    rooms_dict = init_rooms()
    print_rooms(rooms_dict)
    current_room_id = 1
    print(constants.room_assertion + get_room_name(rooms_dict, current_room_id))
    get_new_facts(rooms_dict, current_room_id)
    set_visited(rooms_dict, current_room_id)

    # Une fois que l'agent a recuillis les donnnées, il les imprime.
    while agent.get_suspect() == bool(False):
        print()
        print_rooms(rooms_dict)
        print()
        current_room_id = visit_rooms(rooms_dict, current_room_id)
    print_results()


def print_results():
    print('%s a tué %s dans le %s avec un %s à  %s' % (agent.get_suspect(),
                                                       agent.get_victim(),
                                                       agent.get_crime_room(),
                                                       agent.get_crime_weapon(),
                                                       agent.get_crime_hour()))


if __name__ == "__main__":

    # Cette fonction retourne le format d'une expression logique de premier ordre
    def results_as_string(results):
        res = ''
        for result in results:
            # synrep = syntactic representation
            # semrep = semantic representation
            for (synrep, semrep) in result:
                res += str(semrep)
        return res


    # Cette fonction transforme une phrase en fraçais dans une expression logique du premier ordre
    def to_fol(fact, grammar):
        sent = results_as_string(nltk.interpret_sents(fact, grammar))
        print(sent)
        return sent


    agent = CrimeInference()
    tR = TextRecognition()
    sR = SpeechRecognition()
    speechToText = SpeechToText()
    open_read_file(input(constants.fichier))
    main(agent)
