import { Button, ButtonProps as VdsButtonProps, styled } from '@mui/material';

export const VdsButton = styled(Button)(({ variant, color }: VdsButtonProps) => ({
    fontSize: "16px",
    color: "#FFFFFF",
    letterSpacing: "0.2px",
    lineHeight: "15px",
    fontFamily: "Roboto",
    fontWeight: 500,
    textAlign: "left",
    border: 'none',
    outline: 'none',
    textTransform: 'none',
    padding: '0 16px',
    cursor: 'pointer',
    height: '40px',
    borderRadius: '2px',
    ...(variant === 'outlined' && color === 'primary' && {
        border: '1px solid #0090D1',
        backgroundColor: 'white',
        color: '#0090D1',
        ':hover': {
            backgroundColor: '#0090D1',
            color: 'white',
        },
        ':disabled': {
            color: '#C9D9E8',
            backgroundColor: 'white',
            border: '1px solid #C9D9E8',
        }
    }),
    ...(variant === 'contained' && color === 'primary' && {
        backgroundImage: 'linear-gradient(90deg, #0090D1, #00C3EA)',
        ':hover': {
            background: 'linear-gradient(#00C3EA, #00C3EA)',
        },
        ':disabled': {
            background: '#C9D9E8',
            color: 'white',
        }
    }),
    ...(variant === 'contained' && color === 'secondary' && {
        backgroundColor: '#D82829',
        ':hover': {
            backgroundColor: '#FC4E3D!important'
        }
    })
}));
