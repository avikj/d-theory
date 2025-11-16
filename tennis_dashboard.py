import dash
from dash import html, dcc
import plotly.graph_objects as go
import requests
import pandas as pd
from dash.dependencies import Input, Output
import time

# Mock data for live tennis match (replace with real API)
def get_live_tennis_data():
    # Example: Simulate fetching live score
    # In reality, use requests.get('https://api.example.com/live-tennis')
    return {
        'match': 'Player A vs Player B',
        'score': '6-4, 3-2',
        'aces_player_a': 5,
        'aces_player_b': 3,
        'serve_speed_a': 120,  # km/h
        'serve_speed_b': 115,
        'head_to_head': {'wins_a': 10, 'wins_b': 8}
    }

# Initialize Dash app
app = dash.Dash(__name__)

app.layout = html.Div([
    html.H1('Live Tennis Insights Dashboard', style={'textAlign': 'center'}),
    html.Div(id='live-score', style={'fontSize': '24px', 'textAlign': 'center'}),
    dcc.Graph(id='aces-chart'),
    dcc.Graph(id='serve-speed-chart'),
    dcc.Interval(id='interval-component', interval=10*1000, n_intervals=0)  # Update every 10 seconds
])

@app.callback(
    [Output('live-score', 'children'),
     Output('aces-chart', 'figure'),
     Output('serve-speed-chart', 'figure')],
    Input('interval-component', 'n_intervals')
)
def update_dashboard(n):
    data = get_live_tennis_data()
    
    # Live score text
    score_text = f"{data['match']} - Score: {data['score']}"
    
    # Aces bar chart
    aces_fig = go.Figure(data=[
        go.Bar(name='Aces', x=['Player A', 'Player B'], y=[data['aces_player_a'], data['aces_player_b']])
    ])
    aces_fig.update_layout(title='Aces in Match')
    
    # Serve speed gauge
    speed_fig = go.Figure(go.Indicator(
        mode="gauge+number",
        value=data['serve_speed_a'],
        title={'text': "Player A Serve Speed (km/h)"},
        gauge={'axis': {'range': [None, 140]}}
    ))
    
    return score_text, aces_fig, speed_fig

if __name__ == '__main__':
    app.run()