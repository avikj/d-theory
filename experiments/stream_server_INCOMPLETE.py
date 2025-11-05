import socket
import threading
import os
from datetime import datetime

# Directory for messages
MESSAGE_DIR = "STREAM_MESSAGES"

# Ensure directory exists
os.makedirs(MESSAGE_DIR, exist_ok=True)

# List of client sockets for broadcasting
clients = []
clients_lock = threading.Lock()

def handle_client(client_socket, client_address):
    print(f"New connection from {client_address}")
    with clients_lock:
        clients.append(client_socket)
    try:
        while True:
            data = client_socket.recv(4096)
            if not data:
                break
            message = data.decode('utf-8')
            # Assume message is the .md content
            # Generate timestamp
            timestamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
            filename = f"{timestamp}_AGENT_MESSAGE.md"
            filepath = os.path.join(MESSAGE_DIR, filename)
            with open(filepath, 'w') as f:
                f.write(message)
            print(f"Message saved to {filepath}")
            # Broadcast to all clients
            broadcast(message, client_socket)
    except Exception as e:
        print(f"Error handling client {client_address}: {e}")
    finally:
        with clients_lock:
            clients.remove(client_socket)
        client_socket.close()
        print(f"Connection closed from {client_address}")

def broadcast(message, sender_socket):
    with clients_lock:
        for client in clients:
            if client != sender_socket:
                try:
                    client.sendall(message.encode('utf-8'))
                except:
                    clients.remove(client)

def main():
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.bind(('localhost', 12345))
    server.listen(5)
    print("Server listening on localhost:12345")
    while True:
        client_socket, client_address = server.accept()
        thread = threading.Thread(target=handle_client, args=(client_socket, client_address))
        thread.start()

if __name__ == "__main__":
    main()