import os, threading, webview

def start_server():
    os.environ.setdefault('INTSHUBA_DATA_DIR', os.path.expanduser('~/.intshuba'))
    os.makedirs(os.environ['INTSHUBA_DATA_DIR'], exist_ok=True)
    if not os.environ.get('SECRET_KEY'):
        import secrets
        os.environ['SECRET_KEY'] = secrets.token_hex(32)
    import intshuba
    intshuba.app.run(host='127.0.0.1', port=5100, debug=False, use_reloader=False)

if __name__ == '__main__':
    t = threading.Thread(target=start_server, daemon=True)
    t.start()
    import time; time.sleep(2)
    webview.create_window(
        'Intshuba — 5D Nguni Stone Game',
        'http://127.0.0.1:5100',
        width=1280, height=800, resizable=True
    )
    webview.start()
